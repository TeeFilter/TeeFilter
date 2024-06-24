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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "teefilter_update.h"
#include "certrbpf.h"
#include "state.h"


void harness_update_get_nonce() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  uint64_t nonce;

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  update_get_nonce(&nonce);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


void harness_update_submit_positive() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  struct Update update;

  update_get_nonce(&state.nonce);
  update.nonce = state.nonce;

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assume(update.length <= 1024);

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  bool res = update_submit(&state.bpf, (uint64_t) &update, state.nonce);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assert(res, "harness_update_submit_positive #0");
  __CPROVER_assert(state.bpf.dynamic_rule_enabled, "harness_update_submit_positive #1");
  __CPROVER_assert(state.bpf.dynamic_rule_length == update.length, "harness_update_submit_positive #2");
  __CPROVER_assert(memcmp(state.bpf.dynamic_rule, update.rule, RULE_SIZE) == 0, "harness_update_submit_positive #3");

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


/*
* assume failed nonce verification
*/
void harness_update_submit_negative() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  struct Update update;
  update_get_nonce(&state.nonce);
  // do NOT set nonce in update

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  state.bpf.dynamic_rule_enabled = false;

  __CPROVER_assume(update.length <= 1024);
  __CPROVER_assume(update.nonce != state.nonce);

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  bool res = update_submit(&state.bpf, (uint64_t) &update, state.nonce);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assert(!res, "harness_update_submit_negative #0");
  __CPROVER_assert(state.bpf.dynamic_rule_enabled == false, "harness_update_submit_negative #1");

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}

/*
* assume failed signature verification
*/
void harness_update_submit_negative2() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  struct Update update;
  update_get_nonce(&state.nonce);
  update.nonce = state.nonce;

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  state.bpf.dynamic_rule_enabled = false;

  __CPROVER_assume(update.length <= 1024);

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  bool res = update_submit(&state.bpf, (uint64_t) &update, state.nonce);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  __CPROVER_assert(!res, "harness_update_submit_negative2 #0");
  __CPROVER_assert(state.bpf.dynamic_rule_enabled == false, "harness_update_submit_negative2 #1");

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}


void harness_update_submit_safety() {
  /* -------------------------------------------------------------------------*/
  // Allocate memory and initialize a sane state of the framework
  /* -------------------------------------------------------------------------*/

  struct Update update;

  /* -------------------------------------------------------------------------*/
  // Generate unconstrained inputs
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Preconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Call function under verification
  /* -------------------------------------------------------------------------*/

  bool res = update_submit(&state.bpf, (uint64_t) &update, state.nonce);

  /* -------------------------------------------------------------------------*/
  // Postconditions
  /* -------------------------------------------------------------------------*/

  /* -------------------------------------------------------------------------*/
  // Free allocated memory
  /* -------------------------------------------------------------------------*/
}
