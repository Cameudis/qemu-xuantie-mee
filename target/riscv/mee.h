/*
 * mee.h
 * Copyright (C) 2025 cameudis <cameudis@gmail.com>
 *
 * Distributed under terms of the MIT license.
 */

#ifndef MEE_H
#define MEE_H

extern uint64_t meexc_start;
extern uint64_t meexc_len;

void init_mee(void);
// uint64_t mee_load_ptr(const void *ptr, size_t sz);
uint64_t mee_load_pa(CPURISCVState *env, ram_addr_t pa, size_t sz);
// void mee_store_ptr(void *ptr, uint64_t val, size_t sz);
void mee_store_pa(CPURISCVState *env, ram_addr_t pa, uint64_t val, size_t sz);

#endif /* !MEE_H */
