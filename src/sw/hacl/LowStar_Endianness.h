/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <stdint.h>
// #include <stdbool.h>
// #include "hacl/haclint.h"
#include "bool.h"
#include "compat.h"
#include "lowstar_endianness.h"
#include "types.h"

#ifndef __LowStar_Endianness_H
#define __LowStar_Endianness_H

#include "FStar_UInt128.h"


inline static void store128_le(uint8_t *x0, FStar_UInt128_uint128 x1);

inline static FStar_UInt128_uint128 load128_le(uint8_t *x0);

inline static void store128_be(uint8_t *x0, FStar_UInt128_uint128 x1);

inline static FStar_UInt128_uint128 load128_be(uint8_t *x0);

#define __LowStar_Endianness_H_DEFINED
#endif
