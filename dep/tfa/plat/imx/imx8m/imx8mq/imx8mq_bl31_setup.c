/*
 * Copyright (c) 2018-2019, ARM Limited and Contributors. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include <assert.h>
#include <stdbool.h>

#include <platform_def.h>

#include <arch_helpers.h>
#include <common/bl_common.h>
#include <common/debug.h>
#include <context.h>
#include <drivers/arm/tzc380.h>
#include <drivers/console.h>
#include <drivers/generic_delay_timer.h>
#include <lib/el3_runtime/context_mgmt.h>
#include <lib/mmio.h>
#include <lib/xlat_tables/xlat_tables_v2.h>
#include <plat/common/platform.h>

#include <dram.h>
#include <gpc.h>
#include <imx_aipstz.h>
#include <imx_uart.h>
#include <imx_rdc.h>
#include <imx8m_caam.h>
#include <imx8m_csu.h>
#include <plat_imx8.h>

#define TRUSTY_PARAMS_LEN_BYTES      (4096*2)

static const mmap_region_t imx_mmap[] = {
	MAP_REGION_FLAT(GPV_BASE, GPV_SIZE, MT_DEVICE | MT_RW), /* GPV map */
	MAP_REGION_FLAT(IMX_ROM_BASE, IMX_ROM_SIZE, MT_MEMORY | MT_RO), /* ROM map */
	MAP_REGION_FLAT(OCRAM_S_BASE, OCRAM_S_SIZE, MT_MEMORY | MT_RW), /* ROM map */
	MAP_REGION_FLAT(IMX_AIPS_BASE, IMX_AIPS_SIZE, MT_DEVICE | MT_RW), /* AIPS map */
	MAP_REGION_FLAT(IMX_GIC_BASE, IMX_GIC_SIZE, MT_DEVICE | MT_RW), /* GIC map */
	MAP_REGION_FLAT(IMX_DDRPHY_BASE, IMX_DDR_IPS_SIZE, MT_DEVICE | MT_RW), /* DDRMIX map */

 	MAP_REGION_FLAT(IMX_DRAM_BASE, IMX_DRAM_SIZE, MT_MEMORY | MT_RW | MT_NS),

 	// MAP_REGION_FLAT(IMX_DRAM_BASE, IMX_DRAM_SIZE, MT_NON_CACHEABLE | MT_RW | MT_NS),
	// We map the memory as MT_DEVICE to prevent caching effects when we want
	// to extract data from the NW RAM.
	// MAP_REGION_FLAT(IMX_DRAM_BASE, IMX_DRAM_SIZE, MT_DEVICE | MT_RW | MT_NS),

	MAP_REGION_FLAT(IMX_CAAM_RAM_BASE, IMX_CAAM_RAM_SIZE, MT_MEMORY | MT_RW), /* CAMM RAM */
	MAP_REGION_FLAT(IMX_NS_OCRAM_BASE, IMX_NS_OCRAM_SIZE, MT_MEMORY | MT_RW), /* NS OCRAM */

	// We map the AIPS4 including the TZASC to the EL3 firmware
	MAP_REGION_FLAT(AIPS4_BASE, AIPS4_SIZE, MT_DEVICE | MT_RW),

	// The following leads to a non-booting kernel. We are not sure why.
	// We need to map the NIC later on in this file in during the boot.
	// MAP_REGION_FLAT(IMX_NIC_BASE, IMX_NIC_SIZE, MT_DEVICE | MT_RW), /* Map NIC */

	{0},
};

static const struct aipstz_cfg aipstz[] = {
	{AIPSTZ1_BASE, 0x77777777, 0x77777777, .opacr = {0x0, 0x0, 0x0, 0x0, 0x0}, },
	{AIPSTZ2_BASE, 0x77777777, 0x77777777, .opacr = {0x0, 0x0, 0x0, 0x0, 0x0}, },
	{AIPSTZ3_BASE, 0x77777777, 0x77777777, .opacr = {0x0, 0x0, 0x0, 0x0, 0x0}, },
	{AIPSTZ4_BASE, 0x77777777, 0x77777777, .opacr = {0x0, 0x0, 0x0, 0x0, 0x0}, },
	{0},
};

static entry_point_info_t bl32_image_ep_info;
static entry_point_info_t bl33_image_ep_info;

#if defined (CSU_RDC_TEST)
static void csu_rdc_test(void);
#endif

static uint32_t imx_soc_revision;

int imx_soc_info_handler(uint32_t smc_fid, u_register_t x1, u_register_t x2,
				u_register_t x3)
{
	return imx_soc_revision;
}

#define ANAMIX_DIGPROG		0x6c
#define ROM_SOC_INFO_A0		0x800
#define ROM_SOC_INFO_B0		0x83C
#define OCOTP_SOC_INFO_B1	0x40

static void imx8mq_soc_info_init(void)
{
	uint32_t rom_version;
	uint32_t ocotp_val;

	imx_soc_revision = mmio_read_32(IMX_ANAMIX_BASE + ANAMIX_DIGPROG);
	rom_version = mmio_read_8(IMX_ROM_BASE + ROM_SOC_INFO_A0);
	if (rom_version == 0x10)
		return;

	rom_version = mmio_read_8(IMX_ROM_BASE + ROM_SOC_INFO_B0);
	if (rom_version == 0x20) {
		imx_soc_revision &= ~0xff;
		imx_soc_revision |= rom_version;
		return;
	}

	/* 0xff0055aa is magic number for B1 */
	ocotp_val = mmio_read_32(IMX_OCOTP_BASE + OCOTP_SOC_INFO_B1);
	if (ocotp_val == 0xff0055aa) {
		imx_soc_revision &= ~0xff;
		imx_soc_revision |= 0x21;
		return;
	}
}

/* get SPSR for BL33 entry */
static uint32_t get_spsr_for_bl33_entry(void)
{
	unsigned long el_status;
	unsigned long mode;
	uint32_t spsr;

	/* figure out what mode we enter the non-secure world */
	el_status = read_id_aa64pfr0_el1() >> ID_AA64PFR0_EL2_SHIFT;
	el_status &= ID_AA64PFR0_ELX_MASK;

	mode = (el_status) ? MODE_EL2 : MODE_EL1;

	spsr = SPSR_64(mode, MODE_SP_ELX, DISABLE_ALL_EXCEPTIONS);
	return spsr;
}

static void bl31_tzc380_setup(void)
{
	unsigned int val;

	val = mmio_read_32(IMX_IOMUX_GPR_BASE + IOMUXC_GPR10);
	if ((val & GPR_TZASC_EN) != GPR_TZASC_EN)
		return;

	tzc380_init(IMX_TZASC_BASE);
	/*
	 * Need to substact offset 0x40000000 from CPU address when
	 * programming tzasc region for i.mx8mq. Enable 1G-5G S/NS RW
	 */
	tzc380_configure_region(0, 0x00000000, TZC_ATTR_REGION_SIZE(TZC_REGION_SIZE_4G) |
				TZC_ATTR_REGION_EN_MASK | TZC_ATTR_SP_ALL);

	/* Higher regions have a higher priority level.
	* Therefore, we can just map the ATF region as region 1.
	* https://documentation-service.arm.com/static/5e8e28cffd977155116a6798?token=
	* ATF is from 0xA0000000 to 0xA0200000.
	* However, we need to subtract 0x40000000 as described above:
	* 0xA0000000 - 0x40000000 = 0x60000000
	* This should be 2M.
	* Mark ATF as secure only.
	*/
	INFO("Marking ATF as secure only\n");
	tzc380_configure_region(1, 0x60000000, TZC_ATTR_REGION_SIZE(TZC_REGION_SIZE_2M) |
				TZC_ATTR_REGION_EN_MASK | TZC_ATTR_SP_S_RW);
	INFO("Finished marking ATF as secure only\n");

	// We explicitly disable region 2. It will be used for the ring buffer
	// later on. To prevent crashes because of already marked secure memory
	// during development and many resets of the board, we disable the region
	// here and only enable it during the initialization of the NIC in the
	// Linux kernel
	INFO("Disabling region 2 protection for now\n");
	tzc380_configure_region(2, 0x60200000, TZC_ATTR_REGION_SIZE(TZC_REGION_SIZE_2M) |
				TZC_ATTR_REGION_EN_MASK | TZC_ATTR_SP_ALL);
	INFO("Finished disabling region 2 protection for now\n");

	// Region 3 protection is for the data ring. Disable here and now, enable
	// later on during the setup of the protection service.
	INFO("Disabling region 3 protection for now\n");
	tzc380_configure_region(3, 0x60400000, TZC_ATTR_REGION_SIZE(TZC_REGION_SIZE_8M) |
				TZC_ATTR_REGION_EN_MASK | TZC_ATTR_SP_ALL);
	INFO("Finished disabling region 3 protection for now\n");

	dsb();
}

void bl31_early_platform_setup2(u_register_t arg0, u_register_t arg1,
			u_register_t arg2, u_register_t arg3)
{
#if DEBUG_CONSOLE
	static console_uart_t console;

	console_imx_uart_register(IMX_BOOT_UART_BASE, IMX_BOOT_UART_CLK_IN_HZ,
		IMX_CONSOLE_BAUDRATE, &console);
#endif

  NOTICE("Starting to configure the CSU\n");
	int i;
	/* enable CSU NS access permission */
	for (i = 0; i < 64; i++) {
		mmio_write_32(IMX_CSU_BASE + i * 4, 0x00ff00ff);
	}
	NOTICE("Finishing to configure the CSU\n");

	// We need this here to ensure that we really allow access to the NIC after
	// a boot. When resetting the board from a previous run, we still have a
	// protected NIC and then U-Boot tries to access it and generates a data
	// abort to EL3. Since U-Boot does not have the additions that we introduced
	// it fails. We do not want it actually. Thus, we need to ensure that our
	// platform really writes this permissions to the hardware first.
	dsb();
	isb();
	dsb();

	// NOTICE("To test the custom crash logging framework\n");
	// Allow access to the NIC registers only from the secure world
 	// Note: From the security reference manual, it seems that the upper bytes
	// need to be changed to 0x33. However, the lower ones are the ones from
	// the network card. This is for sure some endianess stuff.
  /* mmio_write_32(IMX_CSU_BASE + 47 * 4, 0x00ff0033);
	dsb();
	dsb();
	dsb(); */

	imx_aipstz_init(aipstz);

	imx8m_caam_init();

	/*
	 * tell BL3-1 where the non-secure software image is located
	 * and the entry state information.
	 */
	bl33_image_ep_info.pc = PLAT_NS_IMAGE_OFFSET;
	bl33_image_ep_info.spsr = get_spsr_for_bl33_entry();
	SET_SECURITY_STATE(bl33_image_ep_info.h.attr, NON_SECURE);

#if defined(SPD_opteed) || defined(SPD_trusty)
	/* Populate entry point information for BL32 */
	SET_PARAM_HEAD(&bl32_image_ep_info, PARAM_EP, VERSION_1, 0);
	SET_SECURITY_STATE(bl32_image_ep_info.h.attr, SECURE);
	bl32_image_ep_info.pc = BL32_BASE;
	bl32_image_ep_info.spsr = 0;

	/* Pass TEE base and size to bl33 */
	bl33_image_ep_info.args.arg1 = BL32_BASE;
	bl33_image_ep_info.args.arg2 = BL32_SIZE;

#ifdef SPD_trusty
	bl32_image_ep_info.args.arg0 = BL32_SIZE;
	bl32_image_ep_info.args.arg1 = BL32_BASE;
#else
	/* Make sure memory is clean */
	mmio_write_32(BL32_FDT_OVERLAY_ADDR, 0);
	bl33_image_ep_info.args.arg3 = BL32_FDT_OVERLAY_ADDR;
	bl32_image_ep_info.args.arg3 = BL32_FDT_OVERLAY_ADDR;
#endif
#endif

	bl31_tzc380_setup();

#if defined (CSU_RDC_TEST)
	csu_rdc_test();
#endif
}

void bl31_plat_arch_setup(void)
{
	mmap_add_region(BL31_BASE, BL31_BASE, (BL31_LIMIT - BL31_BASE),
		MT_MEMORY | MT_RW | MT_SECURE);
	mmap_add_region(BL_CODE_BASE, BL_CODE_BASE, (BL_CODE_END - BL_CODE_BASE),
		MT_MEMORY | MT_RO | MT_SECURE);

	// Map TEE memory
	mmap_add_region(BL32_BASE, BL32_BASE, BL32_SIZE, MT_MEMORY | MT_RW);

	INFO("Mapping NIC\n");
	mmap_add_region(IMX_NIC_BASE, IMX_NIC_BASE, IMX_NIC_SIZE,
		MT_DEVICE | MT_RW | MT_SECURE);
	INFO("Finished mapping NIC\n");

	INFO("Mapping shadow ring buffer\n");
	#define SHADOW_RING_BUFFER_BASE 0xA0200000
	#define SHADOW_RING_BUFFER_LIMIT 0xA0400000
	mmap_add_region(SHADOW_RING_BUFFER_BASE, SHADOW_RING_BUFFER_BASE,
		(SHADOW_RING_BUFFER_LIMIT - SHADOW_RING_BUFFER_BASE), MT_NON_CACHEABLE | MT_RW | MT_SECURE);
	INFO("Finished mapping shadow ring buffer\n");

	INFO("Mapping data ring buffer\n");
	#define DATA_RING_BUFFER_BASE 0xA0400000
	#define DATA_RING_BUFFER_LIMIT 0xA0C00000
	mmap_add_region(DATA_RING_BUFFER_BASE, DATA_RING_BUFFER_BASE,
		(DATA_RING_BUFFER_LIMIT - DATA_RING_BUFFER_BASE), MT_MEMORY | MT_RW | MT_SECURE);
	INFO("Finished mapping data ring buffer\n");

	mmap_add(imx_mmap);

#if USE_COHERENT_MEM
	mmap_add_region(BL_COHERENT_RAM_BASE, BL_COHERENT_RAM_BASE,
		BL_COHERENT_RAM_END - BL_COHERENT_RAM_BASE,
		MT_DEVICE | MT_RW | MT_SECURE);
#endif

	INFO("Enabling the MMU\n");
	/* setup xlat table */
	init_xlat_tables();
	/* enable the MMU */
	enable_mmu_el3(0);
}

void bl31_platform_setup(void)
{
	generic_delay_timer_init();

	/* init the GICv3 cpu and distributor interface */
	plat_gic_driver_init();
	plat_gic_init();

	/* determine SOC revision for erratas */
	imx8mq_soc_info_init();

	/* gpc init */
	imx_gpc_init();

	// dram_info_init(SAVED_DRAM_TIMING_BASE);
}

entry_point_info_t *bl31_plat_get_next_image_ep_info(unsigned int type)
{
	if (type == NON_SECURE)
		return &bl33_image_ep_info;
	if (type == SECURE)
		return &bl32_image_ep_info;

	return NULL;
}

unsigned int plat_get_syscnt_freq2(void)
{
	return mmio_read_32(IMX_SCTR_BASE + CNTFID0_OFF);
}

void bl31_plat_runtime_setup(void)
{
	return;
}

#ifdef SPD_trusty
void plat_trusty_set_boot_args(aapcs64_params_t *args) {
	args->arg0 = BL32_SIZE;
	args->arg1 = BL32_BASE;
	args->arg2 = TRUSTY_PARAMS_LEN_BYTES;
}
#endif

#if defined (CSU_RDC_TEST)
static const struct imx_rdc_cfg rdc_for_test[] = {
	/* Master domain assignment */

	/* peripherals domain permission */

	RDC_PDAPn(RDC_PDAP_CSU, D2R | D2W),

	/* memory region */

	/* Sentinel */
	{0},
};

static const struct imx_csu_cfg csu_cfg_for_test[] = {
	/* peripherals csl setting */
	CSU_CSLx(CSU_CSL_RDC, CSU_SEC_LEVEL_4, LOCKED),
	CSU_CSLx(CSU_CSL_CSU, CSU_SEC_LEVEL_4, LOCKED),
	/* master HP0~1 */

	/* SA setting */

	/* HP control setting */

	/* Sentinel */
	{0}
};

static void csu_rdc_test(void)
{
	imx_csu_init(csu_cfg_for_test);
	imx_rdc_init(rdc_for_test);
}
#endif
