
/*
 * implementation of the PT code for ARM
 */

#include <hw.h>
#include <mmu.h>
#include <utillib.h>
#include "hyper_config.h"

//#include "soc_defs.h" //Maybe put IO_VA_ADDRESS() macro somewhere else?

#define GET_VIRT_ARRAY(phy)  ((uint32_t *) GET_VIRT(phy))

/* for 1MB pages */
#define MEG_BITS 20
#define MEG_SIZE (1UL << MEG_BITS)
#define MEG_MASK (MEG_SIZE - 1)

extern uint32_t __hyper_pt_start__;
extern uint32_t *slpt_va;

/*index 0 reserved for hypervisor
 *Each index holds 256 small pages (totalling 1 MB of space)
 * */
uint32_t l2_index_p = 0;

void map_section(void *page_dir, uint32_t va, uint32_t pa, BOOL cache)
{
	uint32_t page_attr = 0;
	if (cache)
		page_attr =
		    (MMU_AP_SUP_RW << MMU_SECTION_AP_SHIFT) | MMU_FLAG_C |
		    MMU_FLAG_B | MMU_L1_TYPE_SECTION;
	else
		page_attr = ((3 << MMU_SECTION_AP_SHIFT) | MMU_L1_TYPE_SECTION);
	uint32_t *p = (uint32_t *) page_dir;
	p[va >> 20] = (pa & 0xFFF00000) | page_attr;

}

addr_t pt_get_empty_l2()
{
	if ((l2_index_p * 0x400) >= (64 - 16)*1024) {	//Max size of L2 pages. L2 page tables start 16 kB in __hyper_pt_start__.
		printf("Hypervisor: No free l2 page tables!\n");
		while (1);
		return 0;
	} else {
		addr_t index = l2_index_p * 0x400;
		memset((uint32_t *) ((uint32_t) slpt_va + index), 0, 0x400);
		uint32_t l2_base_add = (uint32_t) (GET_PHYS(slpt_va) + index);

		l2_index_p++;
//Remove the following two lines??????
		if ((l2_index_p & 0x2) == 0x2)
			l2_index_p = (l2_index_p & (~0x3)) + 4;
		return l2_base_add;
	}
}

BOOL pt_map(addr_t va, addr_t pa, uint32_t size, uint32_t mem_type)
{
	if (!pt_create_coarse(&__hyper_pt_start__, va, pa, size, mem_type)) {
		printf("Unable to create coarse page\n");
		return FALSE;
	}
	return TRUE;
}

BOOL pt_create_section(addr_t * l1, addr_t va, addr_t pa, uint32_t mem_type)
{
	uint32_t index = (va >> 20);
	uint32_t val = l1[index];
	uint32_t type = MMU_L1_TYPE(val);
	uint32_t domain, ap;

	if ((va & ~(MMU_L1_SECTION_MASK)) == 0 && type == MMU_L1_TYPE_FAULT) {
		val = pa | 0x12;	// 0b1--10
		// if RAM, turn of XN and enable cache and buffer
		if (mem_type == MLT_USER_RAM) {
			val |= MMU_AP_USER_RW << MMU_SECTION_AP_SHIFT;
			val = (val & (~0x10)) | 0xC | (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
			l1[index] = val;
			//            printf("CREATED section for USER%d, val = %x\n", index, val);
			return TRUE;
		}
		if (mem_type == MLT_TRUSTED_RAM) {
			val |= MMU_AP_USER_RW << MMU_SECTION_AP_SHIFT;
			val = (val & (~0x10)) | 0xC | (HC_DOM_TRUSTED << MMU_L1_DOMAIN_SHIFT);
			l1[index] = val;
			//            printf("CREATED section for TRUSTED%d, val = %x\n", index, val);
			return TRUE;
		}
		if (mem_type == MLT_HYPER_RAM) {
			val |= MMU_AP_SUP_RW << MMU_SECTION_AP_SHIFT;	//MMU_AP_SUP_RW = 0x1, MMU_SECTION_AP_SHIFT = 10, which gives RW in PL1, -- in PL0.
			val = (val & (~0x10)) | 0xC | (HC_DOM_DEFAULT << MMU_L1_DOMAIN_SHIFT);
			l1[index] = val;
			//          printf("CREATED section for HYPER%d, val = %x\n", index, val);
			return TRUE;
		}
	}
	printf("Could not allocate section, index=%d va adr=%x pa adr=%x type=%d\n", index, va, pa, type);
	while (1);
	return FALSE;
}

/*
 * functions below are used to build page table from data structure
 */
uint32_t pt_create_coarse(addr_t * pt, addr_t va, addr_t pa, uint32_t size, uint32_t mem_type)
{
	uint32_t *table1 = pt;
	uint32_t index = MMU_L1_INDEX(va);
	uint32_t val = table1[index];
	uint32_t type_old = MMU_L1_TYPE(val);

	uint32_t domain, ap;
	uint32_t flags = MMU_FLAG_B | MMU_FLAG_C;	/*Standard Cache and Buffer on */
	switch (mem_type) {
	case MLT_TRUSTED_RAM:
		domain = HC_DOM_TRUSTED;
		ap = MMU_AP_USER_RW;
		break;

	case MLT_HYPER_RAM:
		domain = HC_DOM_DEFAULT;
		ap = MMU_AP_SUP_RW;
		break;

	case MLT_IO_HYP_REG:
		flags = 1;	/*No cache or buffer in IO an XN = 1 */
		domain = HC_DOM_DEFAULT;
		ap = MMU_AP_SUP_RW;
		break;
	case MLT_IO_RW_REG:
		flags = 1;
		domain = HC_DOM_DEFAULT;
		ap = MMU_AP_USER_RW;
		break;
	case MLT_IO_RO_REG:
		flags = 1;
		domain = HC_DOM_DEFAULT;
		ap = MMU_AP_USER_RO;
		break;
	case MLT_USER_RAM:
		domain = HC_DOM_KERNEL;
		ap = MMU_AP_USER_RW;
		break;
	case MLT_USER_ROM:
		domain = HC_DOM_DEFAULT;
		ap = MMU_AP_USER_RO;
		break;
	default:
		printf("hypervisor/core/hw/cpu/arm/arm_common/pt_create_coarse: Unknown memory type.\n");
//		while (1);
	}
	uint32_t *table2, table2_pa;

	if (type_old == MMU_L1_TYPE_FAULT) {
		/* allocate a new sub-page */
		table2_pa = pt_get_empty_l2();
		if (!table2_pa) {
			printf("hypervisor/core/hw/cpu/arm/arm_common/pt_create_coarse: Cannot allocate new l2 page table.\n");
//			while (1);
			return 0;
		}
		table1[index] = ((uint32_t) (table2_pa) | (domain << MMU_L1_DOMAIN_SHIFT) | MMU_L1_TYPE_COARSE);
	} else {
		/* There is already a mapping to the first level descriptor */
		printf("hypervisor/core/hw/cpu/arm/arm_common/pt_create_coarse: Already mapping of va (0x%x) to pa (0x%x).\n", va, pa);
		table2_pa = MMU_L1_PT_ADDR(table1[index]);
	}

	/*Coarse created, now hand out level 2 page tables for the coarse */
	uint32_t pte;
	uint32_t count = (size >> 12);
	uint32_t slpt_index = ((va & 0x000FF000) >> 12);
	table2 = (uint32_t *) GET_VIRT(table2_pa);

	while (count) {
		pte = (pa | (ap << 4) | flags | MMU_COARSE_TYPE_SMALL);
		table2[slpt_index] = pte;
		slpt_index++;
		pa += 0x1000;
		count--;
	}
	return table2_pa;
}

/*
#define SECTION_SIZE 0x00100000
void pt_create_coarses(addr_t * pt, uint32_t va, uint32_t pa, uint32_t size, uint32_t mem_type) {
	if (size == 0)
		return;

	uint32_t first_mb = va >> 20;
	uint32_t last_mb = (va + size - 1) >> 20;
	uint32_t number_of_mbs = last_mb - first_mb + 1;
	uint32_t first_mb_size = number_of_mbs == 1 ? size : va & 0xFFF00000 + SECTION_SIZE - va;
	uint32_t last_mb_size = size - first_mb_size - (number_of_mbs - 2)*SECTION_SIZE;

	//Mapping first MB.
	pt_create_coarse(pt, (addr_t) va, (addr_t) pa, first_mb_size, mem_type);
	if (number_of_mbs == 1)
		return;

	va = va + first_mb_size;
	pa = pa + first_mb_size;

	//Mapping intermediate MBs.
	uint32_t mb;
	for (mb = 2; mb < number_of_mbs; mb++) {
		pt_create_coarse(pt, (addr_t) va, (addr_t) pa, SECTION_SIZE, mem_type);
		va = va + SECTION_SIZE;
		pa = pa + SECTION_SIZE;
	}

	//Mapping last MB.
	pt_create_coarse(pt, (addr_t) va, (addr_t) pa, last_mb_size, mem_type);
}
*/
