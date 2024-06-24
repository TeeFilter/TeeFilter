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

#include "adapter.h"

#include <lib/smccc.h>
#include <lib/spinlock.h>
#include <common/runtime_svc.h>

#include "prng.h"
#include "teefilter_debug.h"

#include "../teefilter_mmio.h"
#include "../teefilter_init.h"
#include "../state.h"
#include "../teefilter_tx_tos.h"
#include "../teefilter_tx_frs.h"
#include "../teefilter_rx_frs.h"
#include "../teefilter_rx_tos.h"
#include "../teefilter_update.h"
#include "../certrbpf.h"
#include "../checks.h"

#include "../hacl/Ed25519_test.h"

/* -----------------------------------------------------------------------------
* Global variables
* --------------------------------------------------------------------------- */

// The spinlock to serialize access to the EL3 ATF service.
spinlock_t prot_lock;

/* -----------------------------------------------------------------------------
* Constructor
* --------------------------------------------------------------------------- */

static int32_t adapter_svc_setup(void)
{
  spin_lock(&prot_lock);

  INFO("Test Ed25519 from HACL\n");
  Hacl_Ed25519_test();

  INFO("Test PRNG\n");
  prng_test();

  INFO("Initialize TeeFilter (V: 3.56)\n");
  if(!teefilter_init()) {
    ERROR("Could not initialize TeeFilter\n");
	  spin_unlock(&prot_lock);
    return 1;
  }
  certrbpf_init(&state.bpf);

  INFO("Generating an initial nonce\n");
  update_get_nonce(&state.nonce);

	spin_unlock(&prot_lock);
	return 0;
}

/* -----------------------------------------------------------------------------
* Global SMC handler
* --------------------------------------------------------------------------- */

/*
* This function is called whenever an SMC for TeeFilter is executed. It is
* the main entry point.
*/
static uintptr_t adapter_svc_smc_handler(uint32_t smc_fid,
			     u_register_t x1,
			     u_register_t x2,
			     u_register_t x3,
			     u_register_t x4,
			     void *cookie,
			     void *handle,
			     u_register_t flags)
{
  uint32_t oen = GET_SMC_OEN(smc_fid);
	switch (oen) {
  case FUNCID_PROT_NIC_RAW:
    {
      spin_lock(&prot_lock);
			/*
			* We assign the NIC to the SW during the runtime of the kernel (during boot).
			* This way we do not need to adjust U-Boot as well, which also configures the
			* NIC, and, thus, would trap. This is not secure for a productive setup.
			*/
			prot_nic();
      spin_unlock(&prot_lock);
    	SMC_RET0(handle);
      break;
    }
	case FUNCID_WRITE_32_RAW:
    {
      spin_lock(&prot_lock);
			uint32_t val = (uint32_t) x1;
      uint64_t address = (uint64_t) x2;
      teefilter_write32(val, address);
      spin_unlock(&prot_lock);
    	SMC_RET0(handle);
      break;
    }
  case FUNCID_READ_32_RAW:
    {
      spin_lock(&prot_lock);
      uint64_t address = (uint64_t) x1;
      uint32_t val = teefilter_read32(address);
      spin_unlock(&prot_lock);
    	SMC_RET1(handle, (uint64_t) val);
      break;
    }
  case FUNCID_TX_TOS_RAW:
    {
      spin_lock(&prot_lock);
			uint32_t queue = (uint32_t) x1;
			uint32_t current = (uint32_t) x2;
      tx_tos(queue, current);
      spin_unlock(&prot_lock);
    	SMC_RET0(handle);
      break;
    }
  case FUNCID_TX_FRS_RAW:
    {
      spin_lock(&prot_lock);
			uint32_t queue = (uint32_t) x1;
			uint32_t pending_tx_position = (uint32_t) x2;
      tx_frs(queue, pending_tx_position);
      spin_unlock(&prot_lock);
    	SMC_RET0(handle);
      break;
    }
  case FUNCID_RX_FRS_RAW:
    {
      spin_lock(&prot_lock);
			uint32_t queue = (uint32_t) x1;
			uint32_t current = (uint32_t) x2;
			uint32_t budget = (uint32_t) x3;
      rx_frs(queue, current, budget);
      spin_unlock(&prot_lock);
    	SMC_RET0(handle);
      break;
    }
  case FUNCID_RX_TOS_RAW:
    {
      spin_lock(&prot_lock);
			uint32_t queue = (uint32_t) x1;
			uint32_t current = (uint32_t) x2;
			uint32_t received = (uint32_t) x3;
      rx_tos(queue, current, received);
      spin_unlock(&prot_lock);
    	SMC_RET0(handle);
      break;
    }
  case FUNCID_UPDATE_NONCE_RAW:
    {
      spin_lock(&prot_lock);
      update_get_nonce(&state.nonce);
      spin_unlock(&prot_lock);
    	SMC_RET1(handle, state.nonce);
      break;
    }
  case FUNCID_UPDATE_SUBMIT_RAW:
    {
      spin_lock(&prot_lock);
      uint64_t address = (uint64_t) x1;
      uint64_t current_nonce = state.nonce;
      update_submit(&state.bpf, address, current_nonce);
      spin_unlock(&prot_lock);
    	SMC_RET0(handle);
      break;
    }
  default:
    {
      ERROR("Unknown OEN: %d\n", oen);
    	SMC_RET0(handle);
      break;
    }
  }
}

#ifndef MODEL
DECLARE_RT_SVC(
		prot_svc,
		OEN_PROT_START,
		OEN_PROT_END,
		SMC_TYPE_FAST,
		adapter_svc_setup,
		adapter_svc_smc_handler
);
#endif
