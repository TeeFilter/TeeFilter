#include <arch_helpers.h>
#include <endian.h>
#include <common/debug.h>

#include "prng.h"

/*
* Note that the PRNG of this prototype implementation is NOT cryptographically
* secure! In a real-world setup, one needs to exchange the PRNG with a secure
* one!
*
* However, we note that on certain boards, there is already a
* "Arm True Random Number Generator Firmware Interface"
* https://developer.arm.com/documentation/den0098/latest/
*
* As a consequence, generating the RNGs is not even part of TeeFilter but
* already provided by the trusted firmware. One could easily adjust TeeFilter
* to use TRNGs if this interface is available.
*/

/* -----------------------------------------------------------------------------
* Global variables
* --------------------------------------------------------------------------- */

/* -----------------------------------------------------------------------------
* Helper functions
* --------------------------------------------------------------------------- */

/* -----------------------------------------------------------------------------
* From https://de.wikipedia.org/wiki/Multiply-with-carry
* --------------------------------------------------------------------------- */

static uint32_t Q[1038];
static uint32_t c = 123;
static bool initialized = false;

static void MWC1038_init(void) {
  for(uint32_t i=0; i<1038; i++) {
    // Read the current system counter and hash it. This value should be more
    // or less unpredictable.
    uint64_t value = (uint64_t) read_cntpct_el0();
    if(value % 2 == 0) {
       value = htobe64(value);
    }
    // We just take the last four byte of the clock because those are the
    // digits that really make a difference
    uint8_t* dst = (uint8_t*) &Q[i];
    memcpy(dst, &value, 4);
  }
}

static uint32_t MWC1038() {
  static uint32_t i = 1037;
  uint64_t t;
  t = (611376378ULL * Q[i]) + c;
  c = t >> 32;
  if (--i != 0)
      return (Q[i] = t);
  i = 1037;
  uint32_t ret = (Q[0] = t);
  return ret;
}

static int prng_inner(uint8_t* buffer, uint32_t size) {
  if(size == 0) {
    return 0;
  }
  if(!initialized) {
    MWC1038_init();
    initialized = true;
  }
  uint32_t fulls = size / 4;
  for(uint32_t i=0; i<fulls; i++) {
    uint32_t rand = MWC1038();
    uint8_t* ptr = (uint8_t*) &rand;
    for(uint32_t j=0; j<4; j++) {
      buffer[4*i + j] = ptr[j];
    }
  }
  uint32_t remainder = size % 4;
  for(uint32_t i=0; i<remainder; i++) {
    // Just take the first byte, should be enough
    uint32_t rand = MWC1038();
    uint8_t* ptr = (uint8_t*) &rand;
    buffer[4 * fulls + i] = ptr[0];
  }
  return 0;
}

/* -----------------------------------------------------------------------------
* Public Interface.
* --------------------------------------------------------------------------- */

int prng(uint8_t* buffer, uint32_t size) {
  return prng_inner(buffer, size);
}

void prng_test(void) {
    uint8_t buffer[256];
    int ret = prng(buffer, sizeof(buffer));
    if(ret != 0) {
      INFO("test random failed!\n");
    }
    INFO("Random bytes: ");
    for(uint32_t i=0; i<32; i++) {
      printf("%02x", buffer[i]);
    }
    printf("\n");
}
