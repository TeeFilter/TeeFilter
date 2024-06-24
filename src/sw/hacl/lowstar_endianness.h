/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 License. */

#ifndef __LOWSTAR_ENDIANNESS_H
#define __LOWSTAR_ENDIANNESS_H

#include <string.h>
// #include <stdint.h>
#include <stdint.h>
// #include "hacl/haclint.h"
#include "hacllib.h"

/******************************************************************************/
/* Implementing C.fst (part 2: endian-ness macros)                            */
/******************************************************************************/

#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__

/* byte swapping code inspired by:
 * https://github.com/rweather/arduinolibs/blob/master/libraries/Crypto/utility/EndianUtil.h
 * */

#  define htobe32(x) (x)
#  define be32toh(x) (x)
#  define htole32(x)                                                           \
    (__extension__({                                                           \
      uint32_t _temp = (x);                                                    \
      ((_temp >> 24) & 0x000000FF) | ((_temp >> 8) & 0x0000FF00) |             \
          ((_temp << 8) & 0x00FF0000) | ((_temp << 24) & 0xFF000000);          \
    }))
#  define le32toh(x) (htole32((x)))

#  define htobe64(x) (x)
#  define be64toh(x) (x)
#  define htole64(x)                                                           \
    (__extension__({                                                           \
      uint64_t __temp = (x);                                                   \
      uint32_t __low = htobe32((uint32_t)__temp);                              \
      uint32_t __high = htobe32((uint32_t)(__temp >> 32));                     \
      (((uint64_t)__low) << 32) | __high;                                      \
    }))
#  define le64toh(x) (htole64((x)))

/* ... generic little-endian fallback code */
#elif defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__

#  define htole32(x) (x)
#  define le32toh(x) (x)
#  define htobe32(x)                                                           \
    (__extension__({                                                           \
      uint32_t _temp = (x);                                                    \
      ((_temp >> 24) & 0x000000FF) | ((_temp >> 8) & 0x0000FF00) |             \
          ((_temp << 8) & 0x00FF0000) | ((_temp << 24) & 0xFF000000);          \
    }))
#  define be32toh(x) (htobe32((x)))

#  define htole64(x) (x)
#  define le64toh(x) (x)
#  define htobe64(x)                                                           \
    (__extension__({                                                           \
      uint64_t __temp = (x);                                                   \
      uint32_t __low = htobe32((uint32_t)__temp);                              \
      uint32_t __high = htobe32((uint32_t)(__temp >> 32));                     \
      (((uint64_t)__low) << 32) | __high;                                      \
    }))
#  define be64toh(x) (htobe64((x)))

/* ... couldn't determine endian-ness of the target platform */
#else
#  error "Please define __BYTE_ORDER__!"
#endif


/* Loads and stores. These avoid undefined behavior due to unaligned memory
 * accesses, via memcpy. */

inline static uint16_t load16(uint8_t *b) {
  uint16_t x;
  memcpy(&x, b, 2);
  return x;
}

inline static uint32_t load32(uint8_t *b) {
  uint32_t x;
  memcpy(&x, b, 4);
  return x;
}

inline static uint64_t load64(uint8_t *b) {
  uint64_t x;
  memcpy(&x, b, 8);
  return x;
}

inline static void store16(uint8_t *b, uint16_t i) {
  memcpy(b, &i, 2);
}

inline static void store32(uint8_t *b, uint32_t i) {
  memcpy(b, &i, 4);
}

inline static void store64(uint8_t *b, uint64_t i) {
  memcpy(b, &i, 8);
}

/* Legacy accessors so that this header can serve as an implementation of
 * C.Endianness */
#define load16_le(b) (le16toh(load16(b)))
#define store16_le(b, i) (store16(b, htole16(i)))
#define load16_be(b) (be16toh(load16(b)))
#define store16_be(b, i) (store16(b, htobe16(i)))

#define load32_le(b) (le32toh(load32(b)))
#define store32_le(b, i) (store32(b, htole32(i)))
#define load32_be(b) (be32toh(load32(b)))
#define store32_be(b, i) (store32(b, htobe32(i)))

#define load64_le(b) (le64toh(load64(b)))
#define store64_le(b, i) (store64(b, htole64(i)))
#define load64_be(b) (be64toh(load64(b)))
#define store64_be(b, i) (store64(b, htobe64(i)))

/* Co-existence of LowStar.Endianness and FStar.Endianness generates name
 * conflicts, because of course both insist on having no prefixes. Until a
 * prefix is added, or until we truly retire FStar.Endianness, solve this issue
 * in an elegant way. */
#define load16_le0 load16_le
#define store16_le0 store16_le
#define load16_be0 load16_be
#define store16_be0 store16_be

#define load32_le0 load32_le
#define store32_le0 store32_le
#define load32_be0 load32_be
#define store32_be0 store32_be

#define load64_le0 load64_le
#define store64_le0 store64_le
#define load64_be0 load64_be
#define store64_be0 store64_be

#define load128_le0 load128_le
#define store128_le0 store128_le
#define load128_be0 load128_be
#define store128_be0 store128_be

#endif
