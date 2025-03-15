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
// #define MEE_DEBUG
// #define PAT_DEBUG

/* BASICs */

#define CACHE_LINE_LOG2 4
#define CACHE_LINE_SIZE (1<<CACHE_LINE_LOG2)
#define CACHE_LINE_MASK (CACHE_LINE_SIZE - 1)

static bool *bitmap = NULL;
const uint64_t PA_BASE = 0x80000000;
uint64_t PA_END;

uint64_t meexc_start = 0;
uint64_t meexc_len = 0;

AES_KEY enc_key;
AES_KEY dec_key;
// AES_KEY mac_key;

typedef uint8_t Block __attribute__ ((vector_size (16)));
// tweak_keys[Tweak index] = key
static Block tweak_keys[32];

// PAT related structures
#define PAT_LEVELS 4  // Number of levels in the PAT
#define PAT_BLOCK_SIZE CACHE_LINE_SIZE
#define PAT_CHILDREN_PER_NODE 8  // Number of children per node

static __attribute__ ((hot)) void apply_tweak(uint8_t *buf, uint64_t pa)
{
  pa >>= CACHE_LINE_LOG2;
  for (size_t i = 0; i < sizeof(tweak_keys) / sizeof(tweak_keys[0]); ++i) {
    if ((pa >> i) & 1U) {
      ((Block*)buf)[0] ^= tweak_keys[i];
    }
  }
}

static void debug_print(const char *msg, uint64_t pa, uint64_t val[])
{
#ifdef PAT_DEBUG
  fprintf(stderr, "[%s] pa: 0x%lx, value: 0x", msg, pa);
  for (size_t i = 0; i < (CACHE_LINE_SIZE/8); ++i) {
    fprintf(stderr, "%016lx", val[i]);
  }
  fprintf(stderr, "\n");
#endif
}

static void decrypt_block(uint8_t *dest, uint8_t *src, uint64_t pa)
{
  if (bitmap[(pa-PA_BASE) >> CACHE_LINE_LOG2]) {
    AES_decrypt(src, dest, &dec_key);
    apply_tweak(dest, pa);
    debug_print("d", pa, (uint64_t*)dest);
  } else {
    memcpy(dest, src, CACHE_LINE_SIZE);
    return;
  }
}

static void encrypt_block(uint8_t *dest, uint8_t *src, uint64_t pa)
{
  uint8_t tmp_buf[CACHE_LINE_SIZE];
  debug_print("e", pa, (uint64_t*)src);
  bitmap[(pa-PA_BASE) >> CACHE_LINE_LOG2] = 1;
  memcpy(tmp_buf, src, sizeof(tmp_buf));
  apply_tweak(tmp_buf, pa);
  AES_encrypt(tmp_buf, dest, &enc_key);
}

void init_mee(void)
{
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

static inline bool is_exc(uint64_t pa)
{
  return (pa - meexc_start) < meexc_len;
}

/* APIs */

static uint64_t ram_load_ptr(void* ptr, ram_addr_t pa, size_t sz)
{
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

static uint64_t any_load_ptr(void* ptr, ram_addr_t pa, size_t sz)
{
  uint64_t result = 0UL;
  memcpy(&result, ptr, sz);
  return result;
}

uint64_t mee_load_ptr(const void *ptr, size_t sz)
{
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
    if (!bitmap) { bitmap = calloc(mr->size / CACHE_LINE_SIZE, sizeof(*bitmap)); PA_END = PA_BASE + mr->size; }
    return ram_load_ptr(ptr_nc, pa, sz);
  }
}

uint64_t mee_load_pa(CPURISCVState *env, ram_addr_t pa, size_t sz)
{
  CPUState *cs = env_cpu(env);
  uint8_t buf[CACHE_LINE_SIZE] = {};

  MemoryRegion *mr = cs->memory;
  if (!bitmap) { bitmap = calloc(mr->size / CACHE_LINE_SIZE, sizeof(*bitmap)); PA_END = PA_BASE + mr->size; }

  if (pa < PA_BASE || pa >= PA_END || is_exc(pa)) {
    address_space_read(cs->as, pa, MEMTXATTRS_UNSPECIFIED, buf, sz);
    return *(uint64_t*)buf;
  } else {
    uint8_t result[CACHE_LINE_SIZE];
    ram_addr_t base_pa = pa & ~CACHE_LINE_MASK;
    address_space_read(cs->as, base_pa, MEMTXATTRS_UNSPECIFIED, buf, CACHE_LINE_SIZE);
    decrypt_block(result, buf, base_pa);
    return *(uint64_t*)(result + (pa & CACHE_LINE_MASK));
  }
}

static void ram_store_ptr(void *ptr, ram_addr_t pa, uint64_t val, size_t sz)
{
  uint8_t buf[CACHE_LINE_SIZE];

  void *base_ptr = (void *)((uintptr_t)ptr & ~CACHE_LINE_MASK);
  ram_addr_t base_pa = pa & ~CACHE_LINE_MASK;

  size_t off = (uintptr_t)ptr & CACHE_LINE_MASK;

  assert(off + sz <= CACHE_LINE_SIZE);
  decrypt_block(&buf[0], base_ptr, base_pa);
  memcpy(&buf[off], &val, sz);
  encrypt_block(base_ptr, &buf[0], base_pa);
}

static void any_store_ptr(void* ptr, ram_addr_t pa, uint64_t val, size_t sz)
{
  memcpy(ptr, &val, sz);
}

void mee_store_ptr(void *ptr, uint64_t val, size_t sz)
{
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
    if (!bitmap) { bitmap = calloc(mr->size / CACHE_LINE_SIZE, sizeof(*bitmap)); PA_END = PA_BASE + mr->size; }
    ram_store_ptr(ptr, pa, val, sz);
  }
}

void mee_store_pa(CPURISCVState *env, ram_addr_t pa, uint64_t val, size_t sz)
{
  CPUState *cs = env_cpu(env);
  uint8_t buf[CACHE_LINE_SIZE] = {};

  MemoryRegion *mr = cs->memory;
  if (!bitmap) { bitmap = calloc(mr->size / CACHE_LINE_SIZE, sizeof(*bitmap)); PA_END = PA_BASE + mr->size; }

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

