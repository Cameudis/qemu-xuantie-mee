/*
 * mee.c
 * Copyright (C) 2025 cameudis <cameudis@gmail.com>
 *
 * Distributed under terms of the MIT license.
 */

#ifndef CONFIG_USER_ONLY

#include "qemu/osdep.h"
#include "qemu/qemu-print.h"
#include "qemu/ctype.h"
#include "qemu/log.h"
#include "cpu.h"
#include "cpu_vendorid.h"
#include "internals.h"
#include "exec/exec-all.h"
#include "qapi/error.h"
#include "qapi/visitor.h"
#include "qemu/error-report.h"
#include "hw/qdev-properties.h"
#include "hw/core/qdev-prop-internal.h"
#include "exec/tracestub.h"
#include "exec/cpu-common.h"
#include "exec/address-spaces.h"
#include "exec/memory.h"
#include "exec/ramlist.h"
#include "crypto/aes.h"
#include "sys/random.h"

#include "mee.h"

// #define MEE_OFF
#define MEE_DEBUG
// #define PAT_DEBUG

/* BASICs */

#define CACHE_LINE_LOG2 6 // Number of bits of the size of the cache line in bytes
#define CACHE_LINE_SIZE (1 << CACHE_LINE_LOG2) // Size of the cache line in bytes
#define CACHE_LINE_MASK (CACHE_LINE_SIZE - 1)
#define AES_BLOCK_SIZE 16 // Size of the AES block in bytes
#define AES_BLOCK_NUM (CACHE_LINE_SIZE / AES_BLOCK_SIZE) // Number of AES blocks in a cache line
#define MAC_BLOCK_NUM_LOG2 3 // Number of bits of the number of MAC segments
#define MAC_BLOCK_NUM (1 << MAC_BLOCK_NUM_LOG2) // The number of MAC segments (8 bytes per segment)

// x^64 + x^4 + x^3 + x + 1
#define POLY 0x1B
#define UINT64_MSB (1ULL << 63)
#define TRUNC56_MASK ((1ULL << 56) - 1)

const uint64_t PA_BASE = 0x80000000;
uint64_t PA_END;

uint64_t meexc_start = 0;
uint64_t meexc_len = 0;

AES_KEY enc_key;
// AES_KEY dec_key;
uint64_t hash_key[MAC_BLOCK_NUM];

typedef uint8_t Block __attribute__((vector_size(16)));
// tweak_keys[Tweak index] = key
// static Block tweak_keys[32];

#define PAT_LEVELS 4 // Number of levels in the PAT
#define PAT_BLOCK_SIZE CACHE_LINE_SIZE // Size of the pat block in bytes
#define PAT_CHILDREN_PER_NODE_LOG2 MAC_BLOCK_NUM_LOG2 // Number of bits of the number of children per node
#define PAT_CHILDREN_PER_NODE MAC_BLOCK_NUM  // Number of children per node
#define PAT_CHILDREN_MASK (PAT_CHILDREN_PER_NODE - 1)
#define PAT_N_INIT 1 // Initial value of the PAT
#define align(addr) (addr & (~PAT_CHILDREN_MASK)) // Align the address

// contains the tag and counter of each level
typedef struct {
    uint64_t *tag;
    uint64_t *counter;
} PAT_LEVEL;

// counters of the actual memory
static uint64_t *pat_vers = NULL;
// tags of the actual memory
static uint64_t *pd_tags = NULL;
// counters and tags on the tree
static PAT_LEVEL pat_layout[PAT_LEVELS] = {};

/*
static __attribute__((hot)) void apply_tweak(uint8_t *buf, uint64_t pa) {
    pa >>= CACHE_LINE_LOG2;
    for (size_t i = 0; i < sizeof(tweak_keys) / sizeof(tweak_keys[0]); ++i) {
        if ((pa >> i) & 1U) {
            ((Block *)buf)[0] ^= tweak_keys[i];
        }
    }
}
*/

static void debug_print(const char *msg, uint64_t pa, uint64_t val[]) {
#ifdef PAT_DEBUG
    fprintf(stderr, "[%s] pa: 0x%lx, value: 0x", msg, pa);
    for (size_t i = 0; i < (CACHE_LINE_SIZE / 8); ++i) {
        fprintf(stderr, "%016lx", val[i]);
    }
    fprintf(stderr, "\n");
#endif
}

#define TAPS 0x180000C00000001ULL

static uint64_t increment_counter(uint64_t counter) {
    uint64_t msb = (counter >> 55) & 1;
    uint64_t shifted = counter << 1;
    if (msb) {
        shifted ^= TAPS;
    }
    return shifted;
}
/* initialize pat related structures */
static void init_pat_vers(size_t size) {
    pat_vers = calloc(size / CACHE_LINE_SIZE, sizeof(*pat_vers));
    pd_tags = calloc(size / CACHE_LINE_SIZE, sizeof(*pd_tags));

    if (!pat_vers || !pd_tags) {
        fprintf(stderr, "Failed to allocate memory for PAT versions\n");
        exit(EXIT_FAILURE);
    }

    // Initialize the PAT versions
    for (size_t i = 0; i < size / CACHE_LINE_SIZE; ++i) {
        pat_vers[i] = PAT_N_INIT;
    }

    for (size_t i = 0; i < PAT_LEVELS; ++i) {
        // Number of members in the current level
        size_t num_members = size >> (CACHE_LINE_LOG2 + (i + 1) * PAT_CHILDREN_PER_NODE_LOG2);

        pat_layout[i].tag = calloc(num_members, sizeof(*(pat_layout[i].tag)));
        pat_layout[i].counter = calloc(num_members, sizeof(*(pat_layout[i].counter)));

        if (!pat_layout[i].tag || !pat_layout[i].counter) {
            fprintf(stderr, "Failed to allocate memory for PAT layout\n");
            exit(EXIT_FAILURE);
        }

        // Initialize counters
        for (size_t j = 0; j < num_members; ++j) {
            pat_layout[i].counter[j] = PAT_N_INIT;
        }
    }

    PA_END = PA_BASE + size;

#ifdef MEE_DEBUG
    fprintf(stderr, "PAT initialized.\n");
#endif
}

/* get the version of a cache line */
static uint64_t get_pat_ver(uint64_t pa) {
    uint64_t off = pa - PA_BASE;
    uint64_t ver = pat_vers[off >> CACHE_LINE_LOG2];
    return ver;
}
/* update the version of a cache line */
static uint64_t update_pat_ver(uint64_t pa) {
    uint64_t off = pa - PA_BASE;
    return pat_vers[off >> CACHE_LINE_LOG2] = increment_counter(pat_vers[off >> CACHE_LINE_LOG2]);
}
/* get the corresponding level subscript by the offset of the cache line */
static uint64_t get_pat_pos(size_t level, uint64_t off) {
    return off >> ((level + 1) * PAT_CHILDREN_PER_NODE_LOG2);
}
/* GF Multiplication */
static uint64_t mult_GF(uint64_t a, uint64_t b) {
    uint64_t result = 0;
    for (int i = 0; i < 64; ++i) {
        if (b & 1)
            result ^= a;
        a <<= 1;
        if (a & UINT64_MSB)
            a ^= POLY;
        b >>= 1;
    }
    return result;
}
/* generate MAC based on the content, the parent counter and physical address */
static uint64_t calc_MAC(uint64_t *children, uint64_t parent, uint64_t pa) {
    uint8_t nonce[AES_BLOCK_SIZE] = {};
    uint8_t encrypted[AES_BLOCK_SIZE] = {};

    // Set the nonce based on the counter and physical address and encrypt it
    ((uint64_t *)nonce)[0] = parent;
    ((uint64_t *)nonce)[1] = pa;
    AES_encrypt(nonce, encrypted, &enc_key);

    // Take the lower half of the encrypted block and XOR it with the MAC segments
    uint64_t result = *((uint64_t *)encrypted);
    for (size_t i = 0; i < MAC_BLOCK_NUM; ++i)
        result ^= mult_GF(hash_key[i], children[i]);

    // Truncate to 56 bits
    return result & TRUNC56_MASK;
}
/* verify if the MACs on the tree are as expected (skip if the cache line has not been touched) */
static bool verify_mac(uint8_t *data, uint64_t pa, uint64_t ver) {
    // skip the verification if the cache line has not been touched
    if (ver == PAT_N_INIT)
        return true;

    // offset of the cache line
    uint64_t off = (pa - PA_BASE) >> CACHE_LINE_LOG2;
    // the expected MAC value
    uint64_t expected_mac = calc_MAC((uint64_t *)data, ver, pa);

    // verify the level that is not on the tree
    if (expected_mac != pd_tags[off])
        return false;

    // the subscript of the first child
    uint64_t pos_children = align(off);
    // the corresponding parent subscript
    uint64_t pos_parent = get_pat_pos(0, off);

    // verify the on-tree levels
    expected_mac = calc_MAC(&pat_vers[pos_children], pat_layout[0].counter[pos_parent], pos_children);
    if (expected_mac != pat_layout[0].tag[pos_parent]) {
        // fprintf(stderr, "pa: 0x%lx, off: 0x%lx\n", pa & ~((1<<(CACHE_LINE_LOG2+PAT_CHILDREN_PER_NODE_LOG2))-1), off);
        // fprintf(stderr, "pat_vers[align(off >> CACHE_LINE_LOG2)]: 0x%lx_%lx, pat_layout[0].counter[get_pat_pos(0, off)]: 0x%lx\n", pat_vers[align(off >> CACHE_LINE_LOG2)], pat_vers[align(off >> CACHE_LINE_LOG2)+1], pat_layout[0].counter[get_pat_pos(0, off)]);
        // fprintf(stderr, "expected_mac: 0x%lx, pat_layout[0].tag[get_pat_pos(0, off)]: 0x%lx\n", expected_mac, pat_layout[0].tag[get_pat_pos(0, off)]);
        // debug_print("v", pa, (uint64_t *)data);
        return false;
    }
    for (size_t i = 1; i < PAT_LEVELS; ++i) {
        pos_children = align(pos_parent);
        pos_parent = get_pat_pos(i, off);
        expected_mac = calc_MAC(&pat_layout[i - 1].counter[pos_children], pat_layout[i].counter[pos_parent], pos_children);
        if (expected_mac != pat_layout[i].tag[pos_parent])
            return false;
    }
    return true;
}
// /* update a counter */
// static uint64_t update_counter(size_t level, uint64_t pa) {
//     uint64_t off = (pa - PA_BASE) >> CACHE_LINE_LOG2;
//     uint64_t pos = get_pat_pos(level, off);
//     return pat_layout[level].counter[pos] = increment_counter(pat_layout[level].counter[pos]);
// }
/* update MAC tags */
static void update_mac(uint8_t *data, uint64_t pa, uint64_t ver) {
    // offset of the cache line
    uint64_t off = (pa - PA_BASE) >> CACHE_LINE_LOG2;

    // update the level that is not on the tree
    pd_tags[off] = calc_MAC((uint64_t *)data, ver, pa);

    // the subscript of the first child
    uint64_t pos_children = align(off);
    // the corresponding parent subscript
    uint64_t pos_parent = get_pat_pos(0, off);
    // update parent counter
    pat_layout[0].counter[pos_parent] = increment_counter(pat_layout[0].counter[pos_parent]);
    // update parent MAC tag
    pat_layout[0].tag[pos_parent] = calc_MAC(&pat_vers[pos_children], pat_layout[0].counter[pos_parent], pos_children);
    for (size_t i = 1; i < PAT_LEVELS; ++i) {
        pos_children = align(pos_parent);
        pos_parent = get_pat_pos(i, off);
        pat_layout[i].counter[pos_parent] = increment_counter(pat_layout[i].counter[pos_parent]);
        pat_layout[i].tag[pos_parent] = calc_MAC(&pat_layout[i - 1].counter[pos_children], pat_layout[i].counter[pos_parent], pos_children);
    }
    return;
}

static void process_block(uint8_t *dest, uint8_t *src, uint64_t pa, uint64_t ver) {
    Block nonce;
    Block encrypted;

    ((uint64_t *)&nonce)[0] = ver;
    ((uint64_t *)&nonce)[1] = pa;
    AES_encrypt((uint8_t *)&nonce, (uint8_t *)&encrypted, &enc_key);
    *((Block *)dest) = *((Block *)src) ^ encrypted;

    // apply_tweak(dest, pa);
    // debug_print("d", pa, (uint64_t *)dest);
    return;
}
/* AES CTR decrypt with a tweaked counter value (with MAC verification) */
static void decrypt_CTR(uint8_t *dest, uint8_t *src, uint64_t pa) {
    // MAC verification
    uint64_t ver = get_pat_ver(pa);
    if (!verify_mac(src, pa, ver))
        goto verify_failed;

    if (ver != PAT_N_INIT) { // PAT verification passed, decrypt
        debug_print("d", pa, (uint64_t *)dest);
        for (size_t i = 0; i < AES_BLOCK_NUM; ++i) {
            process_block(dest, src, pa, ver);
            dest += AES_BLOCK_SIZE;
            src += AES_BLOCK_SIZE;
            pa += AES_BLOCK_SIZE;
        }
    } else { // PAT verification passed, but ver is n_init
        memcpy(dest, src, CACHE_LINE_SIZE);
    }

    return;

verify_failed:
    assert(0);
}
/* AES CTR encrypt with a tweaked counter value (with MAC update) */
static void encrypt_CTR(uint8_t *dest, uint8_t *src, uint64_t pa) {
    uint64_t ver = update_pat_ver(pa);
    for (size_t i = 0; i < AES_BLOCK_NUM; ++i) {
        process_block(dest, src, pa, ver);
        dest += AES_BLOCK_SIZE;
        src += AES_BLOCK_SIZE;
        pa += AES_BLOCK_SIZE;
    }
    update_mac(dest - AES_BLOCK_NUM * AES_BLOCK_SIZE, pa - AES_BLOCK_NUM * AES_BLOCK_SIZE, ver);
}
/* initialize keys in MEE */
void init_mee(void) {
    unsigned char key_buf[16];
    // Generate a random key for AES encryption
    if (sizeof(key_buf) != (size_t)getrandom(key_buf, sizeof(key_buf), GRND_RANDOM)) {
        abort();
    }
    AES_set_encrypt_key(key_buf, sizeof(key_buf) * 8, &enc_key);
    // AES_set_decrypt_key(key_buf, sizeof(key_buf) * 8, &dec_key);
    /*
    if (sizeof(tweak_keys) != (size_t)getrandom(tweak_keys, sizeof(tweak_keys), GRND_RANDOM)) {
        abort();
    }
    */
    // Generate a random key for MAC
    if (sizeof(hash_key) != (size_t)getrandom(hash_key, sizeof(hash_key), GRND_RANDOM)) {
        abort();
    }

#ifdef MEE_DEBUG
    fprintf(stderr, "MEE initialized.\n");
#endif
}

static inline bool is_exc(uint64_t pa) {
    return (pa - meexc_start) < meexc_len;
}

/* APIs */

static uint64_t ram_load_ptr(void *ptr, ram_addr_t pa, size_t sz) {
    uint64_t result = 0UL;
    uint8_t buf[CACHE_LINE_SIZE];

    ram_addr_t base_pa = pa & ~CACHE_LINE_MASK;
    void *base_ptr = (void *)((uintptr_t)ptr & ~CACHE_LINE_MASK);

    size_t off = (uintptr_t)ptr & CACHE_LINE_MASK;

    assert(off + sz <= CACHE_LINE_SIZE);
    decrypt_CTR(&buf[0], base_ptr, base_pa);
    memcpy(&result, &buf[off], sz);
    return result;
}

static uint64_t any_load_ptr(void *ptr, ram_addr_t pa, size_t sz) {
    uint64_t result = 0UL;
    memcpy(&result, ptr, sz);
    return result;
}

uint64_t mee_load_ptr(const void *ptr, size_t sz) {
    void *ptr_nc = (void *)ptr;
    ram_addr_t pa;
    MemoryRegion *mr = memory_region_from_host(ptr_nc, &pa);
    pa += PA_BASE;

#ifdef MEE_OFF
    return any_load_ptr(ptr_nc, pa, sz);
#endif

    if (!mr || mr->addr != PA_BASE || is_exc(pa)) {
        return any_load_ptr(ptr_nc, pa, sz);
    } else {
        if (!pat_vers)
            init_pat_vers(mr->size);
        return ram_load_ptr(ptr_nc, pa, sz);
    }
}

uint64_t mee_load_pa(CPURISCVState *env, ram_addr_t pa, size_t sz) {
    CPUState *cs = env_cpu(env);
    uint8_t buf[CACHE_LINE_SIZE] = {};

    MemoryRegion *mr = cs->memory;
    if (!pat_vers)
        init_pat_vers(mr->size);

    if (pa < PA_BASE || pa >= PA_END || is_exc(pa)) {
        address_space_read(cs->as, pa, MEMTXATTRS_UNSPECIFIED, buf, sz);
        return *(uint64_t *)buf;
    } else {
        uint8_t result[CACHE_LINE_SIZE];
        ram_addr_t base_pa = pa & ~CACHE_LINE_MASK;
        address_space_read(cs->as, base_pa, MEMTXATTRS_UNSPECIFIED, buf, CACHE_LINE_SIZE);
        decrypt_CTR(result, buf, base_pa);
        return *(uint64_t *)(result + (pa & CACHE_LINE_MASK));
    }
}

static void ram_store_ptr(void *ptr, ram_addr_t pa, uint64_t val, size_t sz) {
    uint8_t buf[CACHE_LINE_SIZE];

    void *base_ptr = (void *)((uintptr_t)ptr & ~CACHE_LINE_MASK);
    ram_addr_t base_pa = pa & ~CACHE_LINE_MASK;

    size_t off = (uintptr_t)ptr & CACHE_LINE_MASK;

    assert(off + sz <= CACHE_LINE_SIZE);
    decrypt_CTR(&buf[0], base_ptr, base_pa);
    memcpy(&buf[off], &val, sz);
    encrypt_CTR(base_ptr, &buf[0], base_pa);
}

static void any_store_ptr(void *ptr, ram_addr_t pa, uint64_t val, size_t sz) {
    memcpy(ptr, &val, sz);
}

void mee_store_ptr(void *ptr, uint64_t val, size_t sz) {
    ram_addr_t pa;
    MemoryRegion *mr = memory_region_from_host(ptr, &pa);
    pa += PA_BASE;

#ifdef MEE_OFF
    any_store_ptr(ptr, pa, val, sz);
    return;
#endif

    if (!mr || mr->addr != PA_BASE || is_exc(pa)) {
        any_store_ptr(ptr, pa, val, sz);
    } else {
        if (!pat_vers)
            init_pat_vers(mr->size);
        ram_store_ptr(ptr, pa, val, sz);
    }
}

void mee_store_pa(CPURISCVState *env, ram_addr_t pa, uint64_t val, size_t sz) {
    CPUState *cs = env_cpu(env);
    uint8_t buf[CACHE_LINE_SIZE] = {};

    MemoryRegion *mr = cs->memory;
    if (!pat_vers)
        init_pat_vers(mr->size);

    if (pa < PA_BASE || pa >= PA_END || is_exc(pa)) {
        address_space_write(cs->as, pa, MEMTXATTRS_UNSPECIFIED, &val, sz);
    } else {
        uint8_t result[CACHE_LINE_SIZE];
        ram_addr_t base_pa = pa & ~CACHE_LINE_MASK;
        address_space_read(cs->as, base_pa, MEMTXATTRS_UNSPECIFIED, buf, CACHE_LINE_SIZE);
        decrypt_CTR(result, buf, base_pa);
        memcpy(result + (pa & CACHE_LINE_MASK), &val, sz);
        encrypt_CTR(buf, result, base_pa);
        address_space_write(cs->as, base_pa, MEMTXATTRS_UNSPECIFIED, buf, CACHE_LINE_SIZE);
    }
}

#endif
