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

#define CACHE_LINE_LOG2 4
#define CACHE_LINE_SIZE (1 << CACHE_LINE_LOG2)
#define CACHE_LINE_MASK (CACHE_LINE_SIZE - 1)
#define MAC_BLOCK_SIZE 2
// x^64 + x^4 + x^3 + x + 1
#define POLY 0x1B

const uint64_t PA_BASE = 0x80000000;
uint64_t PA_END;

uint64_t meexc_start = 0;
uint64_t meexc_len = 0;

AES_KEY enc_key;
AES_KEY dec_key;
uint64_t hash_key[MAC_BLOCK_SIZE] = {0xb6db5eb0283229ae, 0x249325f2909d5fd0};

typedef uint8_t Block __attribute__((vector_size(16)));
// tweak_keys[Tweak index] = key
static Block tweak_keys[32];

// PAT related structures
#define PAT_LEVELS 4 // Number of levels in the PAT
#define PAT_BLOCK_SIZE CACHE_LINE_SIZE
#define PAT_CHILDREN_PER_NODE 2 // Number of children per node
#define PAT_CHILDREN_PER_NODE_LOG2 1
#define PAT_CHILDREN_MASK (PAT_CHILDREN_PER_NODE - 1)
#define PAT_N_INIT 1 // Initial value of the PAT
typedef struct {
    uint64_t *tag;
    uint64_t *counter;
} PAT_LEVEL;

static uint64_t *pat_vers = NULL;
static PAT_LEVEL pat_layout[PAT_LEVELS] = {};
static uint64_t *pd_tags = NULL;

static __attribute__((hot)) void apply_tweak(uint8_t *buf, uint64_t pa) {
    pa >>= CACHE_LINE_LOG2;
    for (size_t i = 0; i < sizeof(tweak_keys) / sizeof(tweak_keys[0]); ++i) {
        if ((pa >> i) & 1U) {
            ((Block *)buf)[0] ^= tweak_keys[i];
        }
    }
}

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

static void init_pat_vers(size_t size) {
    pat_vers = calloc(size / CACHE_LINE_SIZE, sizeof(*pat_vers));
    pd_tags = calloc(size / CACHE_LINE_SIZE, sizeof(*pd_tags));
    assert(pat_vers);
    assert(pd_tags);
    for (size_t i = 0; i < PAT_LEVELS; ++i) {
        pat_layout[i].tag = calloc(size >> (CACHE_LINE_LOG2 + (i + 1) * PAT_CHILDREN_PER_NODE_LOG2), sizeof(*(pat_layout[i].tag)));
        assert(pat_layout[i].tag);
        pat_layout[i].counter = calloc(size >> (CACHE_LINE_LOG2 + (i + 1) * PAT_CHILDREN_PER_NODE_LOG2), sizeof(*(pat_layout[i].counter)));
        assert(pat_layout[i].counter);
    }

    PA_END = PA_BASE + size;

    for (size_t i = 0; i < size / CACHE_LINE_SIZE; ++i) {
        pat_vers[i] = PAT_N_INIT;
    }

    for (size_t i = 0; i < PAT_LEVELS; ++i) {
        for (size_t j = 0; j < (size >> (CACHE_LINE_LOG2 + (i + 1) * PAT_CHILDREN_PER_NODE_LOG2)); ++j)
            pat_layout[i].counter[j] = PAT_N_INIT;
    }

#ifdef MEE_DEBUG
    fprintf(stderr, "PAT initialized.\n");
#endif
}

/* verify PAT and get the related ver */
static uint64_t get_pat_ver(uint64_t pa, bool *success) {
    uint64_t off = pa - PA_BASE;
    uint64_t ver = pat_vers[off >> CACHE_LINE_LOG2];
    *success = true;
    return ver;
}
/* update PAT */
static uint64_t update_pat_ver(uint64_t pa) {
    uint64_t off = pa - PA_BASE;
    return pat_vers[off >> CACHE_LINE_LOG2] = increment_counter(pat_vers[off >> CACHE_LINE_LOG2]);
}

static uint64_t get_pat_pos(size_t level, uint64_t off) {
    return off >> (CACHE_LINE_LOG2 + (level + 1) * PAT_CHILDREN_PER_NODE_LOG2);
}

static uint64_t align(uint64_t addr) {
    return addr & (~PAT_CHILDREN_MASK);
}

static uint64_t mult_GF(uint64_t a, uint64_t b) {
    uint64_t result = 0;
    for (int i = 0; i < 64; ++i) {
        if (b & 1)
            result ^= a;
        a <<= 1;
        if (a & (1ULL << 63))
            a ^= POLY;
        b >>= 1;
    }
    return result;
}

static uint64_t calc_MAC(uint64_t *child, uint64_t parent, uint64_t pa) {
    uint8_t nonce[CACHE_LINE_SIZE] = {};
    uint8_t encrypted[CACHE_LINE_SIZE] = {};

    ((uint64_t *)nonce)[0] = parent;
    ((uint64_t *)nonce)[1] = pa;
    AES_encrypt(nonce, encrypted, &enc_key);

    uint64_t result = *((uint64_t *)encrypted);
    for (size_t i = 0; i < MAC_BLOCK_SIZE; ++i)
        result ^= mult_GF(hash_key[i], child[i]);
    return result & ((1ULL << 56) - 1);
}

static bool verify_mac(uint8_t *data, uint64_t pa, uint64_t ver) {
    if (ver == PAT_N_INIT)
        return true;

    uint64_t off = pa - PA_BASE;
    uint64_t expected_mac = calc_MAC((uint64_t *)data, ver, pa);

    if (expected_mac != pd_tags[off >> CACHE_LINE_LOG2])
        return false;

    expected_mac = calc_MAC(&pat_vers[align(off >> CACHE_LINE_LOG2)], pat_layout[0].counter[get_pat_pos(0, off)], pa & ~((1<<(CACHE_LINE_LOG2+PAT_CHILDREN_PER_NODE_LOG2))-1));
    if (expected_mac != pat_layout[0].tag[get_pat_pos(0, off)]) {
        fprintf(stderr, "pa: 0x%lx, off: 0x%lx\n", pa & ~((1<<(CACHE_LINE_LOG2+PAT_CHILDREN_PER_NODE_LOG2))-1), off);
        fprintf(stderr, "pat_vers[align(off >> CACHE_LINE_LOG2)]: 0x%lx_%lx, pat_layout[0].counter[get_pat_pos(0, off)]: 0x%lx\n", pat_vers[align(off >> CACHE_LINE_LOG2)], pat_vers[align(off >> CACHE_LINE_LOG2)+1], pat_layout[0].counter[get_pat_pos(0, off)]);
        fprintf(stderr, "expected_mac: 0x%lx, pat_layout[0].tag[get_pat_pos(0, off)]: 0x%lx\n", expected_mac, pat_layout[0].tag[get_pat_pos(0, off)]);
        debug_print("v", pa, (uint64_t *)data);
        return false;
    }
    for (size_t i = 1; i < PAT_LEVELS; ++i) {
        expected_mac = calc_MAC(&pat_layout[i - 1].counter[align(get_pat_pos(i - 1, off))], pat_layout[i].counter[get_pat_pos(i, off)], 0);
        if (expected_mac != pat_layout[i].tag[get_pat_pos(i, off)])
            return false;
    }
    return true;
}

static uint64_t update_counter(size_t level, uint64_t pa) {
    uint64_t off = pa - PA_BASE;
    uint64_t pos = get_pat_pos(level, off);
    return pat_layout[level].counter[pos] = increment_counter(pat_layout[level].counter[pos]);
}

static void update_mac(uint8_t *data, uint64_t pa, uint64_t ver) {
    uint64_t off = pa - PA_BASE;
    pd_tags[off >> CACHE_LINE_LOG2] = calc_MAC((uint64_t *)data, ver, pa);
    for (size_t i = 0; i < PAT_LEVELS; ++i)
        update_counter(i, pa);

    pat_layout[0].tag[get_pat_pos(0, off)] = calc_MAC(&pat_vers[align(off >> CACHE_LINE_LOG2)], pat_layout[0].counter[get_pat_pos(0, off)], pa & ~((1<<(CACHE_LINE_LOG2+PAT_CHILDREN_PER_NODE_LOG2))-1));
    for (size_t i = 1; i < PAT_LEVELS; ++i)
        pat_layout[i].tag[get_pat_pos(i, off)] = calc_MAC(&pat_layout[i - 1].counter[align(get_pat_pos(i - 1, off))], pat_layout[i].counter[get_pat_pos(i, off)], 0);
    return;
}

static void decrypt_block(uint8_t *dest, uint8_t *src, uint64_t pa) {
    bool success = false;

    uint64_t ver = get_pat_ver(pa, &success);

    if (!success)
        goto verify_failed;
    if (!verify_mac(src, pa, ver))
        goto verify_failed;

    if (ver != PAT_N_INIT) { // PAT verification passed, decrypt
        // TODO
        AES_decrypt(src, dest, &dec_key);
        apply_tweak(dest, pa);
        debug_print("d", pa, (uint64_t *)dest);
    } else { // PAT verification passed, but ver is n_init
        memcpy(dest, src, CACHE_LINE_SIZE);
    }

    return;

verify_failed:
    assert(0);
}

static void encrypt_block(uint8_t *dest, uint8_t *src, uint64_t pa) {
    uint8_t tmp_buf[CACHE_LINE_SIZE];
    debug_print("e", pa, (uint64_t *)src);

    uint64_t ver = update_pat_ver(pa);

    // TODO
    memcpy(tmp_buf, src, sizeof(tmp_buf));
    apply_tweak(tmp_buf, pa);
    AES_encrypt(tmp_buf, dest, &enc_key);

    update_mac(dest, pa, ver);
}

void init_mee(void) {
    unsigned char key_buf[16];
    if (sizeof(key_buf) != (size_t)getrandom(key_buf, sizeof(key_buf), GRND_RANDOM)) {
        abort();
    }
    AES_set_encrypt_key(key_buf, sizeof(key_buf) * 8, &enc_key);
    AES_set_decrypt_key(key_buf, sizeof(key_buf) * 8, &dec_key);

    if (sizeof(tweak_keys) != (size_t)getrandom(tweak_keys, sizeof(tweak_keys), GRND_RANDOM)) {
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

    assert(off + sz <= 16);
    decrypt_block(&buf[0], base_ptr, base_pa);
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
        decrypt_block(result, buf, base_pa);
        return *(uint64_t *)(result + (pa & CACHE_LINE_MASK));
    }
}

static void ram_store_ptr(void *ptr, ram_addr_t pa, uint64_t val, size_t sz) {
    uint8_t buf[CACHE_LINE_SIZE];

    void *base_ptr = (void *)((uintptr_t)ptr & ~CACHE_LINE_MASK);
    ram_addr_t base_pa = pa & ~CACHE_LINE_MASK;

    size_t off = (uintptr_t)ptr & CACHE_LINE_MASK;

    assert(off + sz <= CACHE_LINE_SIZE);
    decrypt_block(&buf[0], base_ptr, base_pa);
    memcpy(&buf[off], &val, sz);
    encrypt_block(base_ptr, &buf[0], base_pa);
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
        decrypt_block(result, buf, base_pa);
        memcpy(result + (pa & CACHE_LINE_MASK), &val, sz);
        encrypt_block(buf, result, base_pa);
        address_space_write(cs->as, base_pa, MEMTXATTRS_UNSPECIFIED, buf, CACHE_LINE_SIZE);
    }
}

#endif
