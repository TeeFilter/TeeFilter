#ifndef PRNG_H
#define PRNG_H

#include <stdint.h>

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
* Public Interface.
* --------------------------------------------------------------------------- */

int prng(uint8_t* buffer, uint32_t size);
void prng_test(void);

#endif
