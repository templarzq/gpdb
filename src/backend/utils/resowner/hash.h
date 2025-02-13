
//
// hash.h
//
// Copyright (c) 2012 TJ Holowaychuk <tj@vision-media.ca>
//

#ifndef HASH
#define HASH

#include "khash.h"

// pointer hash

//KHASH_MAP_INIT_STR(ptr, void *)

KHASH_MAP_INIT_INT64(i64, void *)

/*
 * Hash type.
 */

typedef khash_t(i64) hash_t;

/*
 * Allocate a new hash.
 */

#define hash_new() kh_init(i64)

/*
 * Destroy the hash.
 */

#define hash_free(self) kh_destroy(i64, self)

/*
 * Hash size.
 */

#define hash_size kh_size

/*
 * Remove all pairs in the hash.
 */

#define hash_clear(self) kh_clear(i64, self)

/*
 * Iterate hash keys and ptrs, populating
 * `key` and `val`.
 */

#define hash_each(self, block) { \
   long int key; \
   void *val; \
    for (khiter_t k = kh_begin(self); k < kh_end(self); ++k) { \
      if (!kh_exist(self, k)) continue; \
      key = kh_key(self, k); \
      val = kh_value(self, k); \
      block; \
    } \
  }

/*
 * Iterate hash keys, populating `key`.
 */

#define hash_each_key(self, block) { \
    long int key; \
    for (khiter_t k = kh_begin(self); k < kh_end(self); ++k) { \
      if (!kh_exist(self, k)) continue; \
      key = kh_key(self, k); \
      block; \
    } \
  }

/*
 * Iterate hash ptrs, populating `val`.
 */

#define hash_each_val(self, block) { \
    void *val; \
    for (khiter_t k = kh_begin(self); k < kh_end(self); ++k) { \
      if (!kh_exist(self, k)) continue; \
      val = kh_value(self, k); \
      block; \
    } \
  }

// protos

void
hash_set(hash_t *self, long int key, void *val);

void *
hash_get(hash_t *self, long int key);

void *
hash_get_begin(hash_t *self);

long int *
hash_get_begin_key(hash_t *self);

int
hash_has(hash_t *self, long int key);

void
hash_del(hash_t *self, long int key);

void
hash_clear(hash_t *self);

#endif /* HASH */
