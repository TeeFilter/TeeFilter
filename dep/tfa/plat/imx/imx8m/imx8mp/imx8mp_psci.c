/*
 * Copyright 2019-2020 NXP
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <stdbool.h>

#include <arch.h>
#include <arch_helpers.h>
#include <common/debug.h>
#include <drivers/delay_timer.h>
#include <lib/mmio.h>
#include <lib/psci/psci.h>

#include <dram.h>
#include <gpc.h>
#include <imx8m_psci.h>
#include <plat_imx8.h>

#if defined(PLAT_imx8mp)
void imx_domain_suspend_finish_a0(const psci_power_state_t *target_state)
{
	uint64_t mpidr = read_mpidr_el1();
	unsigned int core_id = MPIDR_AFFLVL0_VAL(mpidr);

	if (is_local_state_off(SYSTEM_PWR_STATE(target_state))) {
		if (!imx_m4_lpa_active()) {
			imx_noc_wrapper_post_resume(core_id);
			imx_anamix_override(false);
			dram_exit_retention();
			imx_set_sys_lpm(core_id, false);
		} else {
			/* flag 0xD means DSP LPA buffer is in OCRAM */
			if (mmio_read_32(IMX_SRC_BASE + 0x98) == 0xD)
				dram_exit_retention();

			imx_set_sys_wakeup_a0(core_id, false);
		}
	}

	if (!is_local_state_run(CLUSTER_PWR_STATE(target_state))) {
		imx_clear_rbc_count();
		imx_set_cluster_powerdown(core_id, PSCI_LOCAL_STATE_RUN);
	}

	if (is_local_state_off(CORE_PWR_STATE(target_state))) {
		/* mark this core as awake by masking IRQ0 */
		imx_gpc_set_a53_core_awake(core_id);
		imx_set_cpu_lpm(core_id, false);
		plat_gic_cpuif_enable();
	} else {
		write_scr_el3(read_scr_el3() & (~SCR_FIQ_BIT));
		isb();
	}
}
#endif

static const plat_psci_ops_t imx_plat_psci_ops = {
	.pwr_domain_on = imx_pwr_domain_on,
	.pwr_domain_on_finish = imx_pwr_domain_on_finish,
	.pwr_domain_off = imx_pwr_domain_off,
	.validate_ns_entrypoint = imx_validate_ns_entrypoint,
	.validate_power_state = imx_validate_power_state,
	.cpu_standby = imx_cpu_standby,
	.pwr_domain_suspend = imx_domain_suspend,
	.pwr_domain_suspend_finish = imx_domain_suspend_finish,
	.pwr_domain_pwr_down_wfi = imx_pwr_domain_pwr_down_wfi,
	.get_sys_suspend_power_state = imx_get_sys_suspend_power_state,
	.system_reset = imx_system_reset,
	.system_off = imx_system_off,
};

static const plat_psci_ops_t imx_plat_psci_ops_a0 = {
	.pwr_domain_on = imx_pwr_domain_on,
	.pwr_domain_on_finish = imx_pwr_domain_on_finish,
	.pwr_domain_off = imx_pwr_domain_off,
	.validate_ns_entrypoint = imx_validate_ns_entrypoint,
	.validate_power_state = imx_validate_power_state,
	.cpu_standby = imx_cpu_standby,
	.pwr_domain_suspend = imx_domain_suspend,
	.pwr_domain_suspend_finish = imx_domain_suspend_finish_a0,
	.pwr_domain_pwr_down_wfi = imx_pwr_domain_pwr_down_wfi,
	.get_sys_suspend_power_state = imx_get_sys_suspend_power_state,
	.system_reset = imx_system_reset,
	.system_off = imx_system_off,
};

/* export the platform specific psci ops */
int plat_setup_psci_ops(uintptr_t sec_entrypoint,
			const plat_psci_ops_t **psci_ops)
{
	/* sec_entrypoint is used for warm reset */
	imx_mailbox_init(sec_entrypoint);

	*psci_ops = rev_a0 ? &imx_plat_psci_ops_a0 : &imx_plat_psci_ops;

	return 0;
}
