/* Minimal HACL* port (Ed25519 and SHA3) for environments without standard
*  library.
*/

#ifndef HACLLIB_H
#define HACLLIB_H

// #include <linux/types.h>
#include <linux/types.h>

// GCC builtin
/* void memcpy(void *dest, void *src, uint64_t n);
void* memset(void *b, int c, int len); */

void KRML_CHECK_SIZE(uint64_t a, uint64_t b);

#endif
