// SPDX-License-Identifier: GPL-2.0+
/*
 * Copyright 2017 Impinj, Inc
 * Author: Andrey Smirnov <andrew.smirnov@gmail.com>
 *
 * Based on the code of analogus driver:
 *
 * Copyright 2015-2017 Pengutronix, Lucas Stach <kernel@pengutronix.de>
 */

#include <linux/clk.h>
#include <linux/clk-provider.h>
#include <linux/of_device.h>
#include <linux/platform_device.h>
#include <linux/pm_domain.h>
#include <linux/pm_opp.h>
#include <linux/regmap.h>
#include <linux/regulator/consumer.h>
#include <linux/sizes.h>
#include <linux/slab.h>
#include <dt-bindings/power/imx7-power.h>
#include <dt-bindings/power/imx8mq-power.h>

#define GPC_LPCR_A_CORE_BSC			0x000

#define GPC_PGC_CPU_MAPPING		0x0ec

#define IMX7_USB_HSIC_PHY_A_CORE_DOMAIN		BIT(6)
#define IMX7_USB_OTG2_PHY_A_CORE_DOMAIN		BIT(5)
#define IMX7_USB_OTG1_PHY_A_CORE_DOMAIN		BIT(4)
#define IMX7_PCIE_PHY_A_CORE_DOMAIN		BIT(3)
#define IMX7_MIPI_PHY_A_CORE_DOMAIN		BIT(2)

#define IMX8M_PCIE2_A53_DOMAIN			BIT(15)
#define IMX8M_MIPI_CSI2_A53_DOMAIN		BIT(14)
#define IMX8M_MIPI_CSI1_A53_DOMAIN		BIT(13)
#define IMX8M_DISP_A53_DOMAIN			BIT(12)
#define IMX8M_HDMI_A53_DOMAIN			BIT(11)
#define IMX8M_VPU_A53_DOMAIN			BIT(10)
#define IMX8M_GPU_A53_DOMAIN			BIT(9)
#define IMX8M_DDR2_A53_DOMAIN			BIT(8)
#define IMX8M_DDR1_A53_DOMAIN			BIT(7)
#define IMX8M_OTG2_A53_DOMAIN			BIT(5)
#define IMX8M_OTG1_A53_DOMAIN			BIT(4)
#define IMX8M_PCIE1_A53_DOMAIN			BIT(3)
#define IMX8M_MIPI_A53_DOMAIN			BIT(2)

#define GPC_PU_PGC_SW_PUP_REQ		0x0f8
#define GPC_PU_PGC_SW_PDN_REQ		0x104

#define IMX7_USB_HSIC_PHY_SW_Pxx_REQ		BIT(4)
#define IMX7_USB_OTG2_PHY_SW_Pxx_REQ		BIT(3)
#define IMX7_USB_OTG1_PHY_SW_Pxx_REQ		BIT(2)
#define IMX7_PCIE_PHY_SW_Pxx_REQ		BIT(1)
#define IMX7_MIPI_PHY_SW_Pxx_REQ		BIT(0)

#define IMX8M_PCIE2_SW_Pxx_REQ			BIT(13)
#define IMX8M_MIPI_CSI2_SW_Pxx_REQ		BIT(12)
#define IMX8M_MIPI_CSI1_SW_Pxx_REQ		BIT(11)
#define IMX8M_DISP_SW_Pxx_REQ			BIT(10)
#define IMX8M_HDMI_SW_Pxx_REQ			BIT(9)
#define IMX8M_VPU_SW_Pxx_REQ			BIT(8)
#define IMX8M_GPU_SW_Pxx_REQ			BIT(7)
#define IMX8M_DDR2_SW_Pxx_REQ			BIT(6)
#define IMX8M_DDR1_SW_Pxx_REQ			BIT(5)
#define IMX8M_OTG2_SW_Pxx_REQ			BIT(3)
#define IMX8M_OTG1_SW_Pxx_REQ			BIT(2)
#define IMX8M_PCIE1_SW_Pxx_REQ			BIT(1)
#define IMX8M_MIPI_SW_Pxx_REQ			BIT(0)

#define GPC_M4_PU_PDN_FLG		0x1bc

#define GPC_PU_PWRHSK			0x1fc

#define IMX8M_GPU_HSK_PWRDNREQN			BIT(6)
#define IMX8M_VPU_HSK_PWRDNREQN			BIT(5)
#define IMX8M_DISP_HSK_PWRDNREQN		BIT(4)

/*
 * The PGC offset values in Reference Manual
 * (Rev. 1, 01/2018 and the older ones) GPC chapter's
 * GPC_PGC memory map are incorrect, below offset
 * values are from design RTL.
 */
#define IMX7_PGC_MIPI			16
#define IMX7_PGC_PCIE			17
#define IMX7_PGC_USB_HSIC		20

#define IMX8M_PGC_MIPI			16
#define IMX8M_PGC_PCIE1			17
#define IMX8M_PGC_OTG1			18
#define IMX8M_PGC_OTG2			19
#define IMX8M_PGC_DDR1			21
#define IMX8M_PGC_GPU			23
#define IMX8M_PGC_VPU			24
#define IMX8M_PGC_DISP			26
#define IMX8M_PGC_MIPI_CSI1		27
#define IMX8M_PGC_MIPI_CSI2		28
#define IMX8M_PGC_PCIE2			29

#define GPC_PGC_CTRL(n)			(0x800 + (n) * 0x40)
#define GPC_PGC_SR(n)			(GPC_PGC_CTRL(n) + 0xc)

#define GPC_PGC_CTRL_PCR		BIT(0)

#define GPC_CLK_MAX		6

struct imx_pgc_domain;

struct imx_pgc_domain {
	struct generic_pm_domain genpd;
	struct regmap *regmap;
	struct regulator *regulator;
	struct clk *clk[GPC_CLK_MAX];
	int num_clks;

	unsigned int pgc;

	const struct {
		u32 pxx;
		u32 map;
		u32 hsk;
	} bits;

	const int voltage;
	struct device_node *np;

	struct imx_pgc_domain *parent;
	struct regulator *dvfs_reg;
	struct device_node *opp_np[GPC_CLK_MAX];
	unsigned long u_volt;
	unsigned long idle_uv;
	unsigned long idle_uv_min;
	unsigned long idle_uv_max;
};

struct imx_pgc_domain_data {
	const struct imx_pgc_domain *domains;
	size_t domains_num;
	const struct regmap_access_table *reg_access_table;
};

#define to_imx_pgc_domain(_genpd) container_of(_genpd, struct imx_pgc_domain, genpd)
#define genpd_status_on(genpd)		((genpd)->status == GENPD_STATE_ON)

struct gpcv2
{
	struct regmap *regmap;
	const struct imx_pgc_domain_data *domain_data;
	int combined_index;
};

struct uv_freq {
	unsigned long uv;
	unsigned long uv_min;
	unsigned long uv_max;
	unsigned long freq;
};

static void get_max_uv(struct imx_pgc_domain *pd, struct uv_freq *uvf)
{
	struct clk **clks = &pd->clk[0];
	int i = 0;
	struct dev_pm_opp *opp;

	if (!pd->num_clks)
		return;

	while (clks[i] && pd->opp_np[i]) {
		struct uv_freq uv = {
			.uv = 0,
			.uv_min = 0,
			.uv_max = 0,
			.freq = 0,
		};

		uv.freq = clk_get_rate(clks[i]);
		opp = dev_pm_opp_find_freq_ceil_np(&pd->genpd.dev, pd->opp_np[i],
				&uv.freq);
		if (!IS_ERR(opp) && opp) {
			opp_return_volts(opp, &uv.uv, &uv.uv_min, &uv.uv_max);
			dev_dbg(&pd->genpd.dev, "%s: voltage=%ld freq=%ld, clk=%s\n", __func__,
					uv.uv, uv.freq, __clk_get_name(clks[i]));
			if (uvf->uv < uv.uv)
				*uvf = uv;
		} else {
			dev_err(&pd->genpd.dev, "%s: ceil failed, i=%d, freq=%ld, clk=%s\n", __func__,
				i, uv.freq, __clk_get_name(clks[i]));
		}
		i++;
		if (i >= pd->num_clks)
			break;
	}
}

static void rescan_voltage(struct imx_pgc_domain *parent, struct generic_pm_domain *skip)
{
	struct generic_pm_domain *genpd = &parent->genpd;
	struct generic_pm_domain *child_pd;
	struct gpd_link *link;
	struct uv_freq u_volt = {
		.uv = 0,
		.uv_min = 0,
		.uv_max = 0,
		.freq = 0,
	};
	int ret;

	if (!parent->dvfs_reg)
		return;

	list_for_each_entry(link, &genpd->parent_links, parent_node) {
		child_pd = link->child;

		if ((child_pd != skip) && genpd_status_on(child_pd))
			get_max_uv(to_imx_pgc_domain(child_pd), &u_volt);
	}
	get_max_uv(parent, &u_volt);

	if (u_volt.uv && (parent->u_volt != u_volt.uv)) {
		parent->u_volt = u_volt.uv;
		ret = regulator_set_voltage_triplet(parent->dvfs_reg,
				u_volt.uv_min,
				u_volt.uv,
				u_volt.uv_max);
		dev_dbg(&genpd->dev, "%s: voltage=%ld freq=%ld\n", __func__,
				u_volt.uv, u_volt.freq);
	}
}

static void check_voltage(struct imx_pgc_domain *pd)
{
	struct imx_pgc_domain *parent = pd->parent;
	int ret;
	struct uv_freq u_volt = {
		.uv = 0,
		.uv_min = 0,
		.uv_max = 0,
		.freq = 0,
	};

	if (!parent)
		parent = pd;
	if (!parent->dvfs_reg)
		return;

	get_max_uv(pd, &u_volt);

	if (parent->u_volt < u_volt.uv) {
		parent->u_volt = u_volt.uv;
		ret = regulator_set_voltage_triplet(parent->dvfs_reg,
				u_volt.uv_min,
				u_volt.uv,
				u_volt.uv_max);
		dev_dbg(&parent->genpd.dev, "%s: voltage=%ld %ld %ld freq=%ld\n", __func__,
			u_volt.uv_min, u_volt.uv, u_volt.uv_max, u_volt.freq);
	}
}

static int imx_gpc_pu_pgc_sw_pxx_req(struct generic_pm_domain *genpd,
				      bool on)
{
	struct imx_pgc_domain *domain = container_of(genpd,
						      struct imx_pgc_domain,
						      genpd);
	unsigned int offset = on ?
		GPC_PU_PGC_SW_PUP_REQ : GPC_PU_PGC_SW_PDN_REQ;
	const bool enable_power_control = !on;
	int i, ret = 0;
	u32 pxx_req;

	if (domain->regmap)
		regmap_update_bits(domain->regmap, GPC_PGC_CPU_MAPPING,
				   domain->bits.map, domain->bits.map);

	if (domain->regulator && on) {
		ret = regulator_enable(domain->regulator);
		if (ret) {
			dev_err(&genpd->dev, "failed to enable regulator\n");
			goto unmap;
		}
	}

	if (on) {
		check_voltage(domain);

		if (domain->dvfs_reg) {
			ret = regulator_enable(domain->dvfs_reg);
			if (ret) {
				dev_warn(&genpd->dev, "failed to power up the dvfs-reg(%d)\n", ret);
				return ret;
			}
		}
	}

	/* Enable reset clocks for all devices in the domain */
	for (i = 0; i < domain->num_clks; i++)
		clk_prepare_enable(domain->clk[i]);

	if (domain->regmap) {
		if (enable_power_control)
			regmap_update_bits(domain->regmap, GPC_PGC_CTRL(
					   domain->pgc), GPC_PGC_CTRL_PCR,
					   GPC_PGC_CTRL_PCR);

		if (domain->bits.hsk)
			regmap_update_bits(domain->regmap, GPC_PU_PWRHSK,
					   domain->bits.hsk,
					   on ? domain->bits.hsk : 0);

		regmap_update_bits(domain->regmap, offset,
				   domain->bits.pxx, domain->bits.pxx);

		/*
		 * As per "5.5.9.4 Example Code 4" in IMX7DRM.pdf wait
		 * for PUP_REQ/PDN_REQ bit to be cleared
		 */
		ret = regmap_read_poll_timeout(domain->regmap, offset, pxx_req,
					       !(pxx_req & domain->bits.pxx),
					       0, USEC_PER_MSEC);
		if (ret) {
			dev_err(&genpd->dev, "failed to command PGC\n");
			/*
			 * If we were in a process of enabling a
			 * domain and failed we might as well disable
			 * the regulator we just enabled. And if it
			 * was the opposite situation and we failed to
			 * power down -- keep the regulator on
			 */
			on = !on;
		}

		if (enable_power_control)
			regmap_update_bits(domain->regmap, GPC_PGC_CTRL(domain->pgc),
				   GPC_PGC_CTRL_PCR, 0);
	}

	/* Disable reset clocks for all devices in the domain */
	for (i = 0; i < domain->num_clks; i++)
		clk_disable_unprepare(domain->clk[i]);

	if (!on) {
		if (domain->dvfs_reg) {
			ret = regulator_disable(domain->dvfs_reg);
			if (ret)
				dev_warn(&genpd->dev, "failed to power off the dvfs-reg(%d)\n", ret);
		}
		if (domain->opp_np[0] && domain->parent)
			rescan_voltage(domain->parent, genpd);

		if ((domain->u_volt != domain->idle_uv) && domain->dvfs_reg && domain->idle_uv) {
			domain->u_volt = domain->idle_uv;
			ret = regulator_set_voltage_triplet(domain->dvfs_reg,
					domain->idle_uv_min,
					domain->idle_uv,
					domain->idle_uv_max);
			dev_dbg(&genpd->dev, "%s: voltage=%ld\n", __func__, domain->idle_uv);

		}
	}

	if (domain->regulator && !on) {
		int err;

		err = regulator_disable(domain->regulator);
		if (err)
			dev_err(&genpd->dev,
				"failed to disable regulator: %d\n", err);
		/* Preserve earlier error code */
		ret = ret ?: err;
	}
unmap:
	if (domain->regmap)
		regmap_update_bits(domain->regmap, GPC_PGC_CPU_MAPPING,
				   domain->bits.map, 0);
	return ret;
}

static int imx_gpc_pu_pgc_sw_pup_req(struct generic_pm_domain *genpd)
{
	return imx_gpc_pu_pgc_sw_pxx_req(genpd, true);
}

static int imx_gpc_pu_pgc_sw_pdn_req(struct generic_pm_domain *genpd)
{
	return imx_gpc_pu_pgc_sw_pxx_req(genpd, false);
}

static const struct imx_pgc_domain imx7_pgc_domains[] = {
	[IMX7_POWER_DOMAIN_MIPI_PHY] = {
		.genpd = {
			.name      = "mipi-phy",
		},
		.bits  = {
			.pxx = IMX7_MIPI_PHY_SW_Pxx_REQ,
			.map = IMX7_MIPI_PHY_A_CORE_DOMAIN,
		},
		.voltage   = 1000000,
		.pgc	   = IMX7_PGC_MIPI,
	},

	[IMX7_POWER_DOMAIN_PCIE_PHY] = {
		.genpd = {
			.name      = "pcie-phy",
		},
		.bits  = {
			.pxx = IMX7_PCIE_PHY_SW_Pxx_REQ,
			.map = IMX7_PCIE_PHY_A_CORE_DOMAIN,
		},
		.voltage   = 1000000,
		.pgc	   = IMX7_PGC_PCIE,
	},

	[IMX7_POWER_DOMAIN_USB_HSIC_PHY] = {
		.genpd = {
			.name      = "usb-hsic-phy",
		},
		.bits  = {
			.pxx = IMX7_USB_HSIC_PHY_SW_Pxx_REQ,
			.map = IMX7_USB_HSIC_PHY_A_CORE_DOMAIN,
		},
		.voltage   = 1200000,
		.pgc	   = IMX7_PGC_USB_HSIC,
	},
};

static const struct regmap_range imx7_yes_ranges[] = {
		regmap_reg_range(GPC_LPCR_A_CORE_BSC,
				 GPC_M4_PU_PDN_FLG),
		regmap_reg_range(GPC_PGC_CTRL(IMX7_PGC_MIPI),
				 GPC_PGC_SR(IMX7_PGC_MIPI)),
		regmap_reg_range(GPC_PGC_CTRL(IMX7_PGC_PCIE),
				 GPC_PGC_SR(IMX7_PGC_PCIE)),
		regmap_reg_range(GPC_PGC_CTRL(IMX7_PGC_USB_HSIC),
				 GPC_PGC_SR(IMX7_PGC_USB_HSIC)),
};

static const struct regmap_access_table imx7_access_table = {
	.yes_ranges	= imx7_yes_ranges,
	.n_yes_ranges	= ARRAY_SIZE(imx7_yes_ranges),
};

static const struct imx_pgc_domain_data imx7_pgc_domain_data = {
	.domains = imx7_pgc_domains,
	.domains_num = ARRAY_SIZE(imx7_pgc_domains),
	.reg_access_table = &imx7_access_table,
};

static const struct imx_pgc_domain imx8m_pgc_domains[] = {
	[IMX8M_POWER_DOMAIN_MIPI] = {
		.genpd = {
			.name      = "mipi",
		},
		.bits  = {
			.pxx = IMX8M_MIPI_SW_Pxx_REQ,
			.map = IMX8M_MIPI_A53_DOMAIN,
		},
		.pgc	   = IMX8M_PGC_MIPI,
	},

	[IMX8M_POWER_DOMAIN_PCIE1] = {
		.genpd = {
			.name = "pcie1",
		},
		.bits  = {
			.pxx = IMX8M_PCIE1_SW_Pxx_REQ,
			.map = IMX8M_PCIE1_A53_DOMAIN,
		},
		.pgc   = IMX8M_PGC_PCIE1,
	},

	[IMX8M_POWER_DOMAIN_USB_OTG1] = {
		.genpd = {
			.name = "usb-otg1",
		},
		.bits  = {
			.pxx = IMX8M_OTG1_SW_Pxx_REQ,
			.map = IMX8M_OTG1_A53_DOMAIN,
		},
		.pgc   = IMX8M_PGC_OTG1,
	},

	[IMX8M_POWER_DOMAIN_USB_OTG2] = {
		.genpd = {
			.name = "usb-otg2",
		},
		.bits  = {
			.pxx = IMX8M_OTG2_SW_Pxx_REQ,
			.map = IMX8M_OTG2_A53_DOMAIN,
		},
		.pgc   = IMX8M_PGC_OTG2,
	},

	[IMX8M_POWER_DOMAIN_DDR1] = {
		.genpd = {
			.name = "ddr1",
		},
		.bits  = {
			.pxx = IMX8M_DDR1_SW_Pxx_REQ,
			.map = IMX8M_DDR2_A53_DOMAIN,
		},
		.pgc   = IMX8M_PGC_DDR1,
	},

	[IMX8M_POWER_DOMAIN_GPU] = {
		.genpd = {
			.name = "gpu",
		},
		.bits  = {
			.pxx = IMX8M_GPU_SW_Pxx_REQ,
			.map = IMX8M_GPU_A53_DOMAIN,
			.hsk = IMX8M_GPU_HSK_PWRDNREQN,
		},
		.pgc   = IMX8M_PGC_GPU,
	},

	[IMX8M_POWER_DOMAIN_VPU] = {
		.genpd = {
			.name = "vpu",
		},
		.bits  = {
			.pxx = IMX8M_VPU_SW_Pxx_REQ,
			.map = IMX8M_VPU_A53_DOMAIN,
			.hsk = IMX8M_VPU_HSK_PWRDNREQN,
		},
		.pgc   = IMX8M_PGC_VPU,
	},

	[IMX8M_POWER_DOMAIN_DISP] = {
		.genpd = {
			.name = "disp",
		},
		.bits  = {
			.pxx = IMX8M_DISP_SW_Pxx_REQ,
			.map = IMX8M_DISP_A53_DOMAIN,
			.hsk = IMX8M_DISP_HSK_PWRDNREQN,
		},
		.pgc   = IMX8M_PGC_DISP,
	},

	[IMX8M_POWER_DOMAIN_MIPI_CSI1] = {
		.genpd = {
			.name = "mipi-csi1",
		},
		.bits  = {
			.pxx = IMX8M_MIPI_CSI1_SW_Pxx_REQ,
			.map = IMX8M_MIPI_CSI1_A53_DOMAIN,
		},
		.pgc   = IMX8M_PGC_MIPI_CSI1,
	},

	[IMX8M_POWER_DOMAIN_MIPI_CSI2] = {
		.genpd = {
			.name = "mipi-csi2",
		},
		.bits  = {
			.pxx = IMX8M_MIPI_CSI2_SW_Pxx_REQ,
			.map = IMX8M_MIPI_CSI2_A53_DOMAIN,
		},
		.pgc   = IMX8M_PGC_MIPI_CSI2,
	},

	[IMX8M_POWER_DOMAIN_PCIE2] = {
		.genpd = {
			.name = "pcie2",
		},
		.bits  = {
			.pxx = IMX8M_PCIE2_SW_Pxx_REQ,
			.map = IMX8M_PCIE2_A53_DOMAIN,
		},
		.pgc   = IMX8M_PGC_PCIE2,
	},
};

static const struct regmap_range imx8m_yes_ranges[] = {
		regmap_reg_range(GPC_LPCR_A_CORE_BSC,
				 GPC_PU_PWRHSK),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_MIPI),
				 GPC_PGC_SR(IMX8M_PGC_MIPI)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_PCIE1),
				 GPC_PGC_SR(IMX8M_PGC_PCIE1)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_OTG1),
				 GPC_PGC_SR(IMX8M_PGC_OTG1)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_OTG2),
				 GPC_PGC_SR(IMX8M_PGC_OTG2)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_DDR1),
				 GPC_PGC_SR(IMX8M_PGC_DDR1)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_GPU),
				 GPC_PGC_SR(IMX8M_PGC_GPU)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_VPU),
				 GPC_PGC_SR(IMX8M_PGC_VPU)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_DISP),
				 GPC_PGC_SR(IMX8M_PGC_DISP)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_MIPI_CSI1),
				 GPC_PGC_SR(IMX8M_PGC_MIPI_CSI1)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_MIPI_CSI2),
				 GPC_PGC_SR(IMX8M_PGC_MIPI_CSI2)),
		regmap_reg_range(GPC_PGC_CTRL(IMX8M_PGC_PCIE2),
				 GPC_PGC_SR(IMX8M_PGC_PCIE2)),
};

static const struct regmap_access_table imx8m_access_table = {
	.yes_ranges	= imx8m_yes_ranges,
	.n_yes_ranges	= ARRAY_SIZE(imx8m_yes_ranges),
};

static const struct imx_pgc_domain_data imx8m_pgc_domain_data = {
	.domains = imx8m_pgc_domains,
	.domains_num = ARRAY_SIZE(imx8m_pgc_domains),
	.reg_access_table = &imx8m_access_table,
};

static int imx_pgc_get_clocks(struct clk **clks,
		struct device_node *np, struct device *dev)
{
	int i, ret;

	for (i = 0; ; i++) {
		struct clk *clk = of_clk_get(np, i);
		if (IS_ERR(clk))
			break;
		if (i >= GPC_CLK_MAX) {
			dev_err(dev, "more than %d clocks\n",
				GPC_CLK_MAX);
			ret = -EINVAL;
			goto clk_err;
		}
		clks[i] = clk;
	}
	return i;

clk_err:
	while (i)
		clk_put(clks[--i]);

	return ret;
}

static void imx_pgc_put_clocks(struct clk **clks, int num_clks)
{
	while (num_clks)
		clk_put(clks[--num_clks]);
}

static int imx_gpcv2_scan_nodes(struct device *dev,
		struct gpcv2 *gpc,
		struct device_node *pgc_np);

static unsigned char idle_uv[] = "idle-microvolt";

static int imx_pgc_domain_probe(struct platform_device *pdev)
{
	struct imx_pgc_domain *domain = pdev->dev.platform_data;
	struct device *dev = &pdev->dev;
	struct device *parent = dev->parent;
	struct device_node *np = dev->of_node;
	struct gpcv2 *gpc = NULL;
	struct regulator *regulator, *dvfs_reg;
	int num_clks = 0, i;
	struct clk *clks[GPC_CLK_MAX];
	u32 domain_index;
	int vcount;
	u32 microvolt[3];
	int ret;

	/* check things that can defer before allocating domain */
	regulator = devm_regulator_get_optional(dev, "power");
	if (IS_ERR(regulator)) {
		if (PTR_ERR(regulator) != -ENODEV) {
			return dev_err_probe(dev, PTR_ERR(regulator),
					     "Failed to get domain's regulator\n");
		}
		regulator = NULL;
	}

	dvfs_reg = devm_regulator_get_optional(dev, "dvfs");
	if (IS_ERR(dvfs_reg)) {
		if (PTR_ERR(dvfs_reg) != -ENODEV) {
			return dev_err_probe(dev, PTR_ERR(dvfs_reg),
					     "Failed to get dvfs regulator\n");
		}
		dvfs_reg = NULL;
	}

	num_clks = imx_pgc_get_clocks(clks, np, dev);
	if (num_clks < 0) {
		return dev_err_probe(dev, num_clks,
				     "Failed to get domain's clocks\n");
	}

	while (parent) {
		struct gpcv2 *gpc1 = dev_get_drvdata(parent);

		pr_debug("%s:%px %px\n", __func__, gpc1, parent);
		if (gpc && !gpc1)
			break;
		gpc = gpc1;
		parent = parent->parent;
	}

	if (!domain) {
		domain = kzalloc(sizeof(*domain), GFP_KERNEL);
		if (!domain) {
			ret = -ENOMEM;
			goto free_clks;
		}
		ret = of_property_read_string(np, "domain-name", &domain->genpd.name);
		if (ret) {
			dev_err(dev, "get domain name failed\n");
			ret = -EINVAL;
			goto free_clks;
		}
		pdev->dev.platform_data = domain;
	}

	domain_index = gpc->combined_index;
	ret = of_property_read_u32(np, "reg", &domain_index);
	if (!ret)
		domain->regmap = gpc->regmap;

	parent = dev->parent;
	if (parent)
		domain->parent = parent->platform_data;

	domain->regulator = regulator;
	domain->dvfs_reg = dvfs_reg;
	domain->num_clks = num_clks;
	for (i = 0; i < num_clks; i++)
		domain->clk[i] = clks[i];

	domain->genpd.power_on  = imx_gpc_pu_pgc_sw_pup_req;
	domain->genpd.power_off = imx_gpc_pu_pgc_sw_pdn_req;
	domain->np = of_node_get(np);

	ret = pm_genpd_init(&domain->genpd, NULL, true);
	if (ret) {
		dev_err(dev, "Failed to init power domain\n");
		goto free_clks;
	}

	if (regulator && domain->voltage) {
		regulator_set_voltage(regulator,
				      domain->voltage, domain->voltage);
	}

	vcount = of_property_count_u32_elems(np, idle_uv);
	if ((vcount == 1) || (vcount == 3)) {
		ret = of_property_read_u32_array(np, idle_uv, microvolt, vcount);
		if (ret) {
			dev_err(dev, "%s: error parsing %s: %d\n", __func__, idle_uv, ret);
			ret = -EINVAL;
			goto free_clks;
		}
		if (vcount == 1) {
			domain->idle_uv = microvolt[0];
			domain->idle_uv_min = domain->idle_uv;
			domain->idle_uv_max = domain->idle_uv;
		} else {
			domain->idle_uv = microvolt[0];
			domain->idle_uv_min = microvolt[1];
			domain->idle_uv_max = microvolt[2];
		}
	}

	if (domain->num_clks && of_find_property(np, "operating-points-v2", NULL)) {
		ret = dev_pm_opp_of_add_table_np(&domain->genpd.dev, np,
				domain->opp_np, domain->num_clks);
		if (ret && (ret != -ENODEV))
			goto free_clks;
	}

	if (domain->parent) {
		/* add subdomain of parent power domain */
		pm_genpd_add_subdomain(&domain->parent->genpd, &domain->genpd);
	}

	ret = of_genpd_add_provider_simple(np, &domain->genpd);
	if (ret) {
		dev_err(dev, "Failed to add genpd provider\n");
		pm_genpd_remove(&domain->genpd);
		goto free_clks;
	}

	ret = imx_gpcv2_scan_nodes(dev, gpc, np);

free_clks:
	if (ret)
		imx_pgc_put_clocks(clks, num_clks);
	return ret;
}

static int imx_pgc_domain_remove(struct platform_device *pdev)
{
	struct imx_pgc_domain *domain = pdev->dev.platform_data;

	of_genpd_del_provider(domain->np);
	pm_genpd_remove(&domain->genpd);
	imx_pgc_put_clocks(domain->clk, domain->num_clks);
	of_node_put(domain->np);

	return 0;
}

static const struct platform_device_id imx_pgc_domain_id[] = {
	{ "imx-pgc-domain", },
	{ },
};

static struct platform_driver imx_pgc_domain_driver = {
	.driver = {
		.name = "imx-pgc",
	},
	.probe    = imx_pgc_domain_probe,
	.remove   = imx_pgc_domain_remove,
	.id_table = imx_pgc_domain_id,
};
builtin_platform_driver(imx_pgc_domain_driver)

static int imx_gpcv2_scan_nodes(struct device *dev,
		struct gpcv2 *gpc,
		struct device_node *pgc_np)
{
	const struct imx_pgc_domain_data *domain_data = gpc->domain_data;
	struct device_node *np;
	int ret;

	for_each_child_of_node(pgc_np, np) {
		struct platform_device *pd_pdev;
		struct imx_pgc_domain *domain = NULL;
		u32 domain_index = gpc->combined_index;

		ret = of_property_read_u32(np, "reg", &domain_index);
		if (!ret) {
			if (domain_index >= domain_data->domains_num) {
				dev_warn(dev,
					 "Domain index %d is out of bounds\n",
					 domain_index);
				continue;
			}
		} else {
			gpc->combined_index++;
		}
		pd_pdev = platform_device_alloc("imx-pgc-domain",
						domain_index);
		if (!pd_pdev) {
			dev_err(dev, "Failed to allocate platform device\n");
			of_node_put(np);
			return -ENOMEM;
		}

		if (domain_index < domain_data->domains_num) {
			ret = platform_device_add_data(pd_pdev,
					       &domain_data->domains[domain_index],
					       sizeof(domain_data->domains[domain_index]));
			if (ret) {
				platform_device_put(pd_pdev);
				of_node_put(np);
				return ret;
			}
			domain = pd_pdev->dev.platform_data;
		}
		pd_pdev->dev.parent = dev;
		pd_pdev->dev.of_node = np;

		ret = platform_device_add(pd_pdev);
		if (ret) {
			platform_device_put(pd_pdev);
			of_node_put(np);
			return ret;
		}
	}

	return 0;
}

static int imx_gpcv2_probe(struct platform_device *pdev)
{
	const struct imx_pgc_domain_data *domain_data =
			of_device_get_match_data(&pdev->dev);

	struct regmap_config regmap_config = {
		.reg_bits	= 32,
		.val_bits	= 32,
		.reg_stride	= 4,
		.rd_table	= domain_data->reg_access_table,
		.wr_table	= domain_data->reg_access_table,
		.max_register   = SZ_4K,
	};
	struct device *dev = &pdev->dev;
	struct device_node *pgc_np;
	struct regmap *regmap;
	void __iomem *base;
	struct gpcv2 *gpc;
	int ret;

	pgc_np = of_get_child_by_name(dev->of_node, "pgc");
	if (!pgc_np) {
		dev_err(dev, "No power domains specified in DT\n");
		return -EINVAL;
	}

	base = devm_platform_ioremap_resource(pdev, 0);
	if (IS_ERR(base))
		return PTR_ERR(base);

	regmap = devm_regmap_init_mmio(dev, base, &regmap_config);
	if (IS_ERR(regmap)) {
		ret = PTR_ERR(regmap);
		dev_err(dev, "failed to init regmap (%d)\n", ret);
		return ret;
	}
	gpc = devm_kzalloc(dev, sizeof(*gpc), GFP_KERNEL);
	if (!gpc)
		return -ENOMEM;
	gpc->regmap = regmap;
	gpc->domain_data = domain_data;
	gpc->combined_index = domain_data->domains_num;
	dev_set_drvdata(dev, gpc);
	pr_debug("%s:%px %px\n", __func__, gpc, dev);

	return imx_gpcv2_scan_nodes(dev, gpc, pgc_np);
}

static const struct of_device_id imx_gpcv2_dt_ids[] = {
	{ .compatible = "fsl,imx7d-gpc", .data = &imx7_pgc_domain_data, },
	{ .compatible = "fsl,imx8mq-gpc", .data = &imx8m_pgc_domain_data, },
	{ }
};

static struct platform_driver imx_gpc_driver = {
	.driver = {
		.name = "imx-gpcv2",
		.of_match_table = imx_gpcv2_dt_ids,
	},
	.probe = imx_gpcv2_probe,
};
builtin_platform_driver(imx_gpc_driver)
