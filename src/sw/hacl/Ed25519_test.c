#include <stdbool.h>
#include <string.h>
#include <common/debug.h>
#include <arch_helpers.h>

#include "Hacl_Ed25519.h"
#include "Ed25519_test.h"

/* --------------------------------------------------------------------------- */
/* Test Keys                                                                   */
/* --------------------------------------------------------------------------- */

// device_private_key = b'\x11I\x01\xc6\xbcu\x93\xd8d\x93\t\x03\xf2\xb0`\xca\tb\x18\xd9\xcc\x8a\x8c\xe1\x1d\xdb\x03K\xb4\x12H\r'
static uint8_t private_key[] = {17, 73, 1, 198, 188, 117, 147, 216, 100,
  147, 9, 3, 242, 176, 96, 202, 9, 98, 24, 217, 204, 138, 140, 225, 29, 219, 3,
  75, 180, 18, 72, 13, };

// device_public_key = b'.\xbc"\xa5\xd6\xf4\x8f\x07jF\xae|t\xd4_nb\xd1\x9f\x98c)s\xae8\x9di\xe4\xee\xae\xa8\xfa'
static uint8_t public_key[] = {46, 188, 34, 165, 214, 244, 143, 7, 106,
  70, 174, 124, 116, 212, 95, 110, 98, 209, 159, 152, 99, 41, 115, 174, 56, 157,
  105, 228, 238, 174, 168, 250, };


/* --------------------------------------------------------------------------- */
/* Function Definitions                                                        */
/* --------------------------------------------------------------------------- */

#ifdef ED25519_TEST_ENABLED

void Hacl_Ed25519_test() {
  INFO("Testing Ed25519\n");

  // Enable unanligned access
  write_sctlr_el3(read_sctlr_el3() & ~SCTLR_A_BIT);

  uint8_t message[128];
  for(uint32_t i=0; i<128; i++) {
    message[i] = 'A';
  }

  uint8_t signature[64];

  INFO("Sign the message\n");
  Hacl_Ed25519_sign(signature, private_key, 128, message);

  INFO("Verify the signature\n");
  bool verify = Hacl_Ed25519_verify(public_key, 128, message, signature);
  if(verify) {
    INFO("The verification was successful!\n");
  } else {
    INFO("The verification failed!\n");
  }

  INFO("Break the signature\n");
  signature[0x7] = 0x8;

  INFO("Verify the signature again\n");
  verify = Hacl_Ed25519_verify(public_key, 128, message, signature);
  if(!verify) {
    INFO("The verification did not succeed! (this is good)\n");
  } else {
    INFO("The false verification failed! (this is not good)\n");
  }

  INFO("Finished testing Ed25519\n");
}

#else

void Hacl_Ed25519_test() {
}

#endif
