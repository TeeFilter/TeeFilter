/*******************************************************************************
* Copyright (C) 2022-2024 Jonas Röckl <joroec@gmx.net>
* This program is free software; you can redistribute it and/or
* modify it under the terms of the GNU General Public License
* as published by the Free Software Foundation; either version 2
* of the License, or (at your option) any later version.
*
* This program is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
* GNU General Public License for more details.
*
* You should have received a copy of the GNU General Public License
* along with this program; If not, see <http://www.gnu.org/licenses/>.
*******************************************************************************/

#include <stdint.h>
#include <string.h>
#include <common/debug.h>

#include "teefilter_update.h"

#include "checks.h"
#include "certrbpf.h"
#include "hacl/Hacl_Ed25519.h"
#include "plat/prng.h"

/* -----------------------------------------------------------------------------
* KEY MATERIAL
* --------------------------------------------------------------------------- */

// BASE64: RQwD+n5Uv6NqfFTTiBTvX5w/vsLNa5IQGvGe260/VAc=
static uint8_t ed25519_hub_public_key[] = {
  0x45, 0x0c, 0x03, 0xfa, 0x7e, 0x54, 0xbf, 0xa3, 0x6a, 0x7c, 0x54, 0xd3,
  0x88, 0x14, 0xef, 0x5f, 0x9c, 0x3f, 0xbe, 0xc2, 0xcd, 0x6b, 0x92, 0x10,
  0x1a, 0xf1, 0x9e, 0xdb, 0xad, 0x3f, 0x54, 0x07
};

// BASE64: hGCbtob+DIWX9drlVTMVwsVukn8dvs2TcIWFgZg6yCY=
//static uint8_t ed25519_hub_private_key[] = {
//  0x84, 0x60, 0x9b, 0xb6, 0x86, 0xfe, 0x0c, 0x85, 0x97, 0xf5, 0xda, 0xe5,
//  0x55, 0x33, 0x15, 0xc2, 0xc5, 0x6e, 0x92, 0x7f, 0x1d, 0xbe, 0xcd, 0x93,
//  0x70, 0x85, 0x85, 0x81, 0x98, 0x3a, 0xc8, 0x26
//};

/* -----------------------------------------------------------------------------
* UPDATE GET NONCE
* --------------------------------------------------------------------------- */

void update_get_nonce(uint64_t* nonce) {
  INFO("Generate nonce\n");
  prng((uint8_t*) nonce, sizeof(uint64_t));
  INFO("Nonce: %llx\n", *nonce);
}

/* -----------------------------------------------------------------------------
* SUBMIT UPDATE
* --------------------------------------------------------------------------- */

/*
* bpf must be initialized. TFA guarantees that.
*/
bool update_submit(struct bpf* bpf, uint64_t address, uint64_t current_nonce) {
  INFO("Received update request\n");

  // In the model, we do not differentiate between NW and SW memory.
  // We verify that "is_nw_ram_region" is correct in a seperate proof.
  #ifdef MODEL
  __CPROVER_assert(__CPROVER_rw_ok((uint8_t*) address, sizeof(struct Update)), "update_submit #1");
  __CPROVER_assert(__CPROVER_rw_ok(bpf), "update_submit #2");
  #else
  if(!is_nw_ram_region(address, sizeof(struct Update))) {
    ERROR("update_get_nonce: Not a valid NW RAM region: %llx\n", address);
    return false;
  }
  #endif

  struct Update* nw_update = (struct Update*) address;
  struct Update update;
  memcpy(&update, nw_update, sizeof(struct Update));

  #ifndef MODEL_SKIP_VERIFICATION
  // Verify the signature
  INFO("Verify the Ed25519 signature\n");
  #ifdef MODEL_ASSUME_FAILED_VERIFICATION
  bool verify = false;
  #else
  bool verify = Hacl_Ed25519_verify(ed25519_hub_public_key, SIGNED_SIZE,
      (uint8_t*) &update, (uint8_t*) &update.signature);
  #endif
  if(!verify) {
     INFO("The Ed25519 verification failed!\n");
     return false;
  }
  #endif
  INFO("The Ed25519 verification succeeded!\n");

  // Verify the nonce
  if(update.nonce != current_nonce) {
     INFO("The nonce is not valid!\n");
     return false;
  }
  INFO("The nonce is valid!\n");

  if(update.length > RULE_SIZE) {
    INFO("Invalid size\n");
    return false;
  }

  // We can now install the new rule
  INFO("Update the rule!\n");
  certrbpf_update(bpf, update.rule, update.length);
  INFO("Rule updated!\n");

  return true;
}
