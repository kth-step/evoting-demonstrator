#include "hyper.h"
#include "dmmu.h"
#include "mmu.h"

extern virtual_machine *curr_vm;
extern uint32_t *flpt_va;
void find_mapping_l1(uint32_t pa);
void remove_aps_l1(uint32_t pa);
uint32_t invalidate_l2_entries_with_invalid_aps(uint32_t l2_base_pa_add);
#if 0
#define DEBUG_MMU_L1_Free
#define DEBUG_MMU_L1_CREATE
#define DEBUG_MMU_L1_SWITCH
#define DEBUG_MMU_SET_L1
#endif

/*Get physical address from Linux virtual address*/
#define LINUX_PA(va) ((va) - (addr_t)(curr_vm->config->firmware->vstart) + (addr_t)(curr_vm->config->firmware->pstart))
/*Get virtual address from Linux physical address*/
#define LINUX_VA(pa) ((pa) - (addr_t)(curr_vm->config->firmware->pstart) + (addr_t)(curr_vm->config->firmware->vstart))

//uint32_t va_limit_x = 0xc2000000;
//uint32_t va_limit_x = 0xc07c714c;
//uint32_t va_limit_x = 0xc0469000;
#define pa_in_kernel_code(pa) (pa < curr_vm->config->firmware->pstart + (curr_vm->config->runtime_kernel_ex_va_top - curr_vm->config->firmware->vstart))
#define pa_below_1to1_l2s(pa) (pa < curr_vm->config->firmware->pstart + curr_vm->config->pa_initial_l2_offset)
#define number_of_1to1_l2s (curr_vm->config->firmware->psize >> 20)	//112
#define size_of_1to1_l2s (number_of_1to1_l2s*2*1024)				//224kB
#define pa_above_1to1_l2s(pa) (pa >= curr_vm->config->firmware->pstart + curr_vm->config->pa_initial_l2_offset + size_of_1to1_l2s)

uint32_t L2_MAP(uint32_t table2_pa, uint32_t i, uint32_t page_pa, uint32_t attrs) {
	uint32_t attrs1 = attrs;

	// We are not mapping kernel code memory
	if (!pa_in_kernel_code(page_pa)) {
		if (!pa_below_1to1_l2s(table2_pa)) {
			if (!pa_above_1to1_l2s(table2_pa)) {
				// It is one of the L2 pts built by linux_init for the 1to1 mapping
				attrs1 |= 0b1;
			}
		}
	}

	return dmmu_l2_map_entry(table2_pa, i, page_pa, attrs1);
}

BOOL virtual_address_mapped(uint32_t va, virtual_machine * curr_vm) {
	uint32_t guest_pt_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, guest_pt_pa);
	uint32_t guest_pt_va = mmu_guest_pa_to_va(guest_pt_pa, curr_vm->config);
	uint32_t index = VA_TO_L1_IDX(va);
	if (*((uint32_t *)(guest_pt_va + index*4)) != 0x0) {
		printf("Hypervisor virtual_address_mapped: Virtual address 0x%x is mapped: 0x%x\n", va, *((uint32_t *)(guest_pt_va + index*4)));
		uint32_t l1_entry = *((uint32_t *)(guest_pt_va + index*4));
		uint32_t l2_idx = (va << 12) >> 24;
		uint32_t l2d_va = (l1_entry & 0xFFFFFC00) - 0x81000000 + 0xC0000000;
		uint32_t l2d = *((uint32_t *) l2d_va);

		if (l2d != 0x0) {
			printf("L2 descriptor at 0x%x mapped = 0x%x.\n", l2d_va, l2d);
		} else {
			printf("L2 descriptor unmapped.\n");
			while (1);
		}

		return TRUE;
	} else {
		printf("Hypervisor virtual_address_mapped: Virtual address 0x%x is not mapped by entry 0x%x at 0x%x with index 0x%x\n", va, *((uint32_t *)(guest_pt_va + index*4)), guest_pt_va + index*4, index);
		return FALSE;
	}
}

void dump_L1pt(virtual_machine * curr_vm) {
	uint32_t guest_pt_va, guest_pt_pa, index;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, guest_pt_pa);
	guest_pt_va = mmu_guest_pa_to_va(guest_pt_pa, curr_vm->config);
	printf("dump_L1pt: guest_pt_pa = %x\n", guest_pt_pa);
	printf("dump_L1pt: guest_pt_va = %x\n", guest_pt_va);
	for (index = 0; index < 4096; index++)
		if (*((uint32_t *)(guest_pt_va + index)) != 0x0)
			printf("add %x %x \n", index, *((uint32_t *)(guest_pt_va + index)));
}

void dump_L2pt(addr_t l2_base, virtual_machine * curr_vm) {
	uint32_t l2_idx, l2_desc_pa_add, l2_desc_va_add, l2_desc;
	for (l2_idx = 512; l2_idx < 1024; l2_idx++) {
		l2_desc_pa_add = L2_DESC_PA(l2_base, l2_idx);
		l2_desc_va_add = mmu_guest_pa_to_va(l2_desc_pa_add, curr_vm->config);
		l2_desc = *((uint32_t *) l2_desc_va_add);
		printf("L2 Entry at %x + %x is %x \n", l2_base, l2_idx, l2_desc);
	}
}

void dump_L2pts(virtual_machine * curr_vm) {
	uint32_t guest_pt_va, guest_pt_pa, index;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, guest_pt_pa);
	guest_pt_va = mmu_guest_pa_to_va(guest_pt_pa, curr_vm->config);
	for (index = 0; index < 4096; index++)
		if (*((uint32_t *)(guest_pt_va + index)) != 0x0)
			dump_L2pt(MMU_L1_PT_ADDR(*((uint32_t *)(guest_pt_va + index))), curr_vm);
}

void hypercall_dyn_switch_mm(addr_t table_base, uint32_t context_id)
{
#ifdef DEBUG_MMU_L1_SWITCH
	printf("Hypercall switch PGD\t table_base:%x context_id:%x\n",
	       table_base, context_id);
#endif

	/*Switch the TTB and set context ID */
	if (dmmu_switch_mm(table_base & L1_BASE_MASK)) {
		printf("\n\tCould not switch MM\n");
		dmmu_switch_mm(table_base & L1_BASE_MASK);
	}
	COP_WRITE(COP_SYSTEM, COP_CONTEXT_ID_REGISTER, context_id);	//Set context ID
	isb();
}

/* Free Page table, Make it RW again */
void hypercall_dyn_free_pgd(addr_t * pgd_va)
{
#ifdef DEBUG_MMU_L1_Free
	printf("\n\t\t\tHypercall FREE PGD\n\t\t pgd:%x \n", pgd_va);
#endif
	uint32_t i, clean_va, err;

	uint32_t page_offset = curr_vm->guest_info.page_offset;

	/*First get the physical address of the lvl 2 page by
	 * looking at the index of the pgd location. Then set
	 * 4 lvl 2 pages to read write*/

	addr_t *master_pgd_va;
	/*Get master page table */
	master_pgd_va = (addr_t *) (curr_vm->config->pa_initial_l1_offset + page_offset);
	addr_t *l1_pt_entry_for_desc = (addr_t *) & master_pgd_va[(addr_t) pgd_va >> MMU_L1_SECTION_SHIFT];
	uint32_t l1_desc_entry = *l1_pt_entry_for_desc;

	/*Get level 2 page table address */

	uint32_t table2_pa = MMU_L1_PT_ADDR(l1_desc_entry);
	uint32_t table2_idx = (table2_pa - (table2_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT;
	table2_idx *= 0x100;	/*256 pages per L2PT */

	uint32_t l2_entry_idx = (((uint32_t) pgd_va << 12) >> 24) + table2_idx;

	uint32_t *l2_page_entry = (uint32_t *) (mmu_guest_pa_to_va(table2_pa & L2_BASE_MASK, (curr_vm->config)));
	uint32_t page_pa = MMU_L2_SMALL_ADDR(l2_page_entry[l2_entry_idx]);

	uint32_t attrs = MMU_L2_TYPE_SMALL;
	attrs |= (MMU_FLAG_B | MMU_FLAG_C);
	attrs |= MMU_AP_USER_RW << MMU_L2_SMALL_AP_SHIFT;

	for (i = l2_entry_idx; i < l2_entry_idx + 4; i++) {
		if (err = dmmu_l2_unmap_entry(table2_pa & L2_BASE_MASK, i)) {
			printf("\n\tCould not unmap L2 entry in new PGD, err = %d\n", err);
			while (1);
		}
	}

	if (err = dmmu_unmap_L1_pt(LINUX_PA((addr_t) pgd_va))) {
		printf("\n\thypercall_dyn_free_pgd0: Could not unmap L1 PT in free pgd at pgd_pa = 0x%x, pgd_va = 0x%x, err = %d\n", LINUX_PA((addr_t) pgd_va), pgd_va, err);
		printf("curr_vm->config->firmware->vstart = 0x%x\n", curr_vm->config->firmware->vstart);
		printf("curr_vm->config->firmware->pstart = 0x%x\n", curr_vm->config->firmware->pstart);
		printf("pa = 0x%x\n", (addr_t) pgd_va - (addr_t) curr_vm->config->firmware->vstart + (addr_t) curr_vm->config->firmware->pstart);
		while (1);
	}

	for (i = l2_entry_idx; i < l2_entry_idx + 4; i++, page_pa += 0x1000) {
		if (err = L2_MAP(table2_pa & L2_BASE_MASK, i, page_pa, attrs)) {
			printf("\n\tCould not map L2 entry in new pgd, err = %d\n", err);
			while (1);
		}

		clean_va = LINUX_VA(MMU_L2_SMALL_ADDR(l2_page_entry[i]));
		CacheDataInvalidateBuff(&l2_page_entry[i], 4);
		dsb();

		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA, clean_va);
		COP_WRITE(COP_SYSTEM, COP_BRANCH_PRED_INVAL_ALL, clean_va);	/*Update cache with new values */
		dsb();
		isb();
	}

#ifdef AGGRESSIVE_FLUSHING_HANDLERS
	hypercall_dcache_clean_area((uint32_t) pgd_va, 0x4000);
#endif
}

/*New pages for processes, copys kernel space from master pages table
 *and cleans the cache, set these pages read only for user */
//#define DEBUG_MMU_L1_CREATE 
void hypercall_dyn_new_pgd(addr_t * pgd_va)
{
#ifdef DEBUG_MMU_L1_CREATE
	printf("*** Hypercall new PGD pgd: va:0x%x pa:0x%x\n", pgd_va, LINUX_PA((addr_t) pgd_va));
#endif

	/*If the requested page is in a section page, we need to modify it to lvl 2 pages
	 *so we can modify the access control granularity */
	uint32_t i, end, table2_idx, table2_pa, err = 0;

	addr_t *master_pgd_va;
	addr_t phys_start = curr_vm->config->firmware->pstart;
	addr_t page_offset = curr_vm->guest_info.page_offset;
	addr_t linux_va;
	/*Get master page table */
	master_pgd_va = (addr_t *) (curr_vm->config->pa_initial_l1_offset + page_offset);
	addr_t *l1_pt_entry_for_desc = (addr_t *) & master_pgd_va[(addr_t) pgd_va >> MMU_L1_SECTION_SHIFT];
	uint32_t l1_desc_entry = *l1_pt_entry_for_desc;

	if (l1_desc_entry & MMU_L1_TYPE_SECTION){ 
		printf("****ERROR: Linux 1-to-1 memory mapped by section\n");
		while (1);
	}
	
	//TODO: Exit if the l1 descriptor is unmapped.

	/*Get the index of the page entry to make read only */

	table2_pa = MMU_L1_PT_ADDR(l1_desc_entry);
	table2_idx = (table2_pa - (table2_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT;
	table2_idx *= 0x100;	/*256 pages per L2PT */

	uint32_t l2_entry_idx = (((uint32_t) pgd_va << 12) >> 24) + table2_idx;

	uint32_t *l2_page_entry = (uint32_t *) (mmu_guest_pa_to_va(table2_pa & L2_BASE_MASK, (curr_vm->config)));
	uint32_t page_pa = MMU_L2_SMALL_ADDR(l2_page_entry[l2_entry_idx]);

	addr_t clean_va;

	//TODO: This must be done only if the ap is 3 (RW)
#ifdef DEBUG_MMU_L1_CREATE
	printf("\n\tRemapping as read only the page:%x\n",page_pa);
#endif
	for (i = l2_entry_idx; i < l2_entry_idx + 4; i++, page_pa += 0x1000) {
		if ((err = dmmu_l2_unmap_entry(table2_pa & L2_BASE_MASK, i))) {
			printf("\n\tCould not unmap L2 entry in new PGD err:%d\n", err);
			while (1);
		}

		uint32_t ro_attrs = 0xE | (MMU_AP_USER_RO << MMU_L2_SMALL_AP_SHIFT);


		if ((err = L2_MAP(table2_pa & L2_BASE_MASK, i, page_pa, ro_attrs))) {
			printf("\n\tCould not map L2 entry in new pgd err:%d\n", err);
			while (1);
		}

		clean_va = LINUX_VA(MMU_L2_SMALL_ADDR(l2_page_entry[i]));
		CacheDataInvalidateBuff(&l2_page_entry[i], 4);
		dsb();

		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA, clean_va);
		COP_WRITE(COP_SYSTEM, COP_BRANCH_PRED_INVAL_ALL, clean_va);	/*Update cache with new values */
		dsb();
		isb();
	}

	/* Page table 0x0 - 0x4000
	 * Reset user space 0-0x2fc0
	 * 0x2fc0 = 0xBF000000 END OF USER SPACE
	 * Copy kernel, IO and hypervisor mappings
	 * 0x2fc0 - 0x4000
	 * */
	uint32_t l1_va_add = mmu_guest_pa_to_va(LINUX_PA((addr_t) pgd_va), curr_vm->config);
	memset((void *)l1_va_add, 0, 0x2fc0);
	memcpy((void *)(l1_va_add + 0x2fC0), (uint32_t *) ((uint32_t) (master_pgd_va) + 0x2fc0), 0x1040);
	/*Clean dcache on whole table */
	clean_and_invalidate_cache();
	if ((err = dmmu_create_L1_pt(LINUX_PA((addr_t) pgd_va)))) {
		printf("\n\tCould not create L1 pt in new pgd in %x err:%d\n", LINUX_PA((addr_t) pgd_va), err);
		printf("\n\tMaster PGT:%x\n", LINUX_PA((addr_t) master_pgd_va));
		print_all_pointing_L1(LINUX_PA((addr_t) pgd_va), 0xfff00000);
		while (1) ;
	}
}

/*In ARM linux pmd refers to pgd, ARM L1 Page table
 *Linux maps 2 pmds at a time  */
// #define DEBUG_SET_PMD
/* @pmd: Virtual address of first-level page table entry.
 * @desc: Descriptor entry to write to @pmd.
 */
void hypercall_dyn_set_pmd(addr_t * pmd, uint32_t desc)
{
#ifdef DEBUG_SET_PMD
	printf("*** Hypercall set_pmd: va:0x%x pa:0x%x\n", pmd, LINUX_PA((addr_t) pmd));
#endif
	uint32_t err;
	uint32_t switch_back = 0;
	addr_t l1_entry, *l1_pt_entry_for_desc;
	addr_t curr_pgd_pa, *pgd_va, attrs;
	uint32_t l1_pt_idx_for_desc, l1_desc_entry, phys_start;

	phys_start = curr_vm->config->firmware->pstart;							//0x8100_0000
	addr_t page_offset = curr_vm->guest_info.page_offset;					//0xC000_0000
	uint32_t page_offset_idx = (page_offset >> MMU_L1_SECTION_SHIFT) * 4;	//(0xC000_0000 >> 20) << 2 (left shift by 2 to get l1_desc_pa)

	/*Page attributes */
	uint32_t l2_rw_attrs = MMU_L2_TYPE_SMALL;
	l2_rw_attrs |= (MMU_FLAG_B | MMU_FLAG_C);
	l2_rw_attrs |= MMU_AP_USER_RW << MMU_L2_SMALL_AP_SHIFT;

	/*Get page table for pmd */
	//pgd_va = pmd & 0xFFFF_C000 = virtual address of start of first-level page table to modify.
	pgd_va = (addr_t *) (((addr_t) pmd) & L1_BASE_MASK);	/*Mask with 16KB alignment to get PGD */

	/*Get current page table */
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, (uint32_t) curr_pgd_pa);	//Physical base address of l1-page table.
	addr_t master_pgd_va = (curr_vm->config->pa_initial_l1_offset + page_offset);	//Virtual base address of Linux l1-page table.

	/*Switch to the page table that we want to modify if we are not in it */
	if ((LINUX_PA((addr_t) pmd & L1_BASE_MASK)) != curr_pgd_pa) {	//If l1-page table to modify is not the current one in use.
		/*This means that we are setting a pmd on another pgd, current
		 * API does not allow that, so we have to switch the physical ttb0
		 * back and forth */
		COP_WRITE(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, LINUX_PA((addr_t) pgd_va));	// Set TTB0
		isb();
		switch_back = 1;
	}

	/*Page table entry to set, if the desc is 0 we have to
	 * get it from the pgd*/
	if (desc != 0)
		l1_entry = desc;	//If not unmap, take new descriptor.
	else
		l1_entry = *pmd;	//If unmap, take old descriptor.

	//Offset MB index of second-level page table identified by descriptor.
	l1_pt_idx_for_desc = ((l1_entry - phys_start) >> MMU_L1_SECTION_SHIFT) * 4;

if (l1_pt_idx_for_desc != (((l1_entry & 0xFFF00000) - (phys_start & 0xFFF00000)) >> MMU_L1_SECTION_SHIFT) * 4) {
printf("Differ: l1_entry = 0x%x, phys_start = 0x%x\n", l1_entry, phys_start);
while (1);
}

	//l1_pt_entry_for_desc =
	//Virtual base address of l1-table to modify +
	//Offset index of second-level page table +
	//Virtual index of first virtual address =
	//Virtual address of l1-descriptor mapping the l2 page table of l1_entry.
	l1_pt_entry_for_desc = (addr_t *) ((addr_t) pgd_va + l1_pt_idx_for_desc + page_offset_idx);
	//L1-descriptor mapping the l2 table of l1_entry.
	l1_desc_entry = *l1_pt_entry_for_desc;

	if (l1_desc_entry & MMU_L1_TYPE_SECTION){ 
		printf("****ERROR: Linux 1-to-1 memory mapped by section\n");
		while (1);
	}
	//TODO: Exit if the l1 entry is unmapped.

	//Remove 10 LSBs of l1_entry and identify the virtual address of the page table identified by the l1-entry =
	//Virtual address of the l2 page table mapped to by l1_entry.
	uint32_t *desc_va = (uint32_t *) LINUX_VA(MMU_L1_PT_ADDR(l1_entry));

	COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA, desc_va);
	COP_WRITE(COP_SYSTEM, COP_BRANCH_PRED_INVAL_ALL, desc_va);
	dsb();
	isb();

	/*We need to make sure the new L2 PT is unreferenced */
#ifdef DEBUG_SET_PMD
	printf("\t desc is 0x%x\n", desc);
	printf("\t desc_va is 0x%x\n", desc_va);
#endif

	//desc_va_idx = MB index of virtual address of l2 page table mapped to by l1_entry.
	addr_t desc_va_idx = MMU_L1_SECTION_IDX((addr_t) desc_va);
	//l2pt_pa = Physical address of l2 page table mapping the l2 page table identified by l1_entry.
	addr_t l2pt_pa = MMU_L1_PT_ADDR(pgd_va[desc_va_idx]);
	//l2pt_va = Virtual address of l2 page table mapping the l2 page table identified by l1_entry.
	addr_t *l2pt_va = (addr_t *) (mmu_guest_pa_to_va(l2pt_pa, curr_vm->config));

	//l2_idx = l2 index field of l2 page table address identified by l1_entry.
	uint32_t l2_idx = ((uint32_t) l1_entry << 12) >> 24;

	//L2 descriptor identifying the physical location of the l2 page table identified by l1_entry.
	uint32_t l2entry_desc = l2pt_va[l2_idx];

	/*Get index of physical L2PT */
	//l2pt_pa & L2_BASE_MASK = l2pt_pa & 0xFFFF_F000 = base address of page containing the page table at l2pt_pa.
	//l2pt_pa - (l2pt_pa & L2_BASE_MASK) = byte offset of l2 page table from start of page containing the l2 page table.
	//table2_idx = number of kB offset of l2 page table from start of page containing the l2 page table.
	uint32_t table2_idx = (l2pt_pa - (l2pt_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT; //2 or 3
	//If table2_idx = 0, then l2 page table is located at beginning then no l2
	//entries before it, and if 1, then 1024 l2 entries before it.
	table2_idx *= 0x100;	/*256 pages per L2PT */

	//TODO: Fix the method to read the ap
	/*If page entry for L2PT is RW, unmap it and make it RO so we can create a L2PT */
	//(l2entry_desc >> 4) & 0xFF = AP[1:0]. If AP[1:0] == 3, then read-write since hypercall clears on AP[2].
	if (((l2entry_desc >> 4) & 0xff) == 3) {
#ifdef DEBUG_SET_PMD
		printf("\n\tRemapping as read only the page:%x\n",l2entry_desc);
#endif
		//ph_block is 4kb page index of the page storing the l2 page table identified by l1_entry.
		uint32_t ph_block = PA_TO_PH_BLOCK(l2entry_desc);
		dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);
#ifdef DEBUG_SET_PMD
		printf("\n\tCounter :%d\n",bft_entry->refcnt);
#endif

		uint32_t l2_desc_pa_add = L2_IDX_TO_PA((uint32_t) l2pt_pa & L2_BASE_MASK, table2_idx + l2_idx);
		//Virtual address of level-2 descriptor via the address space used by the
		//hypervisor to read Linux memory.
		uint32_t l2_desc_va_add = mmu_guest_pa_to_va(l2_desc_pa_add, (curr_vm->config));
		//Read level-2 descriptor.
		uint32_t l2_desc = *((uint32_t *) l2_desc_va_add);

		if (err = dmmu_l2_unmap_entry((uint32_t) l2pt_pa & L2_BASE_MASK, table2_idx + l2_idx)) {
			printf("\n\tCould not unmap L2 entry in set PMD, err = %d\n", err);
			while (1);
		}
//		uint32_t desc_pa = MMU_L2_SMALL_ADDR(desc);
		uint32_t desc_pa = MMU_L2_SMALL_ADDR(l2_desc);
		uint32_t ro_attrs = 0xE | (MMU_AP_USER_RO << MMU_L2_SMALL_AP_SHIFT);

		err = L2_MAP((uint32_t) l2pt_pa & L2_BASE_MASK, table2_idx + l2_idx, desc_pa, ro_attrs);
		if (err) {
			printf("\n\thypercall_dyn_set_pmd0: Could not map L2 entry in set PMD, err = %d\n", err);
			while (1);
		}
	}

	if (desc != 0) {	//Not unmap l1 entry.
		err = dmmu_create_L2_pt(MMU_L2_SMALL_ADDR(desc));
		if (err == ERR_MMU_REFERENCED) {
			invalidate_l2_entries_with_invalid_aps(MMU_L2_SMALL_ADDR(desc) & L2_BASE_MASK);
			remove_aps_l1(MMU_L2_SMALL_ADDR(desc) & L2_BASE_MASK);
			err = dmmu_create_L2_pt(MMU_L2_SMALL_ADDR(desc) & L2_BASE_MASK);	//Mark identified L2-page table (from l1-entry) as L2.
			if (err) {
				printf("hypercall_dyn_set_pmd0.5: err = %d with l2pt_hw_entry_pa = 0x%x\n", err, MMU_L2_SMALL_ADDR(desc) & L2_BASE_MASK);
				print_all_pointing_L2(MMU_L2_SMALL_ADDR(desc) & L2_BASE_MASK, 0xFFFFFFFF);
				while (1);
			}
		} else if (err != SUCCESS_MMU && err != ERR_MMU_ALREADY_L2_PT) {
			printf("hypercall_dyn_set_pmd1: Could not create L2PT in set pmd at %x, err = %d\n", MMU_L2_SMALL_ADDR(desc), err);

#ifdef DEBUG_MMU_SET_L1
			printf("Hypercall set PMD pmd:%x val:%x \n", pmd, desc);
#endif

			print_all_pointing_L1(MMU_L2_SMALL_ADDR(desc), 0xfffff000);
			print_all_pointing_L2(MMU_L2_SMALL_ADDR(desc), 0xfffff000);
			
			while (1) ;
		}
	}

	attrs = desc & 0x3FF;	/*Mask out addresss */

	/*Get virtual address of the translation for pmd */
	//(Virtual byte address of l1-descriptor - virtual byte address of pgd) / 4 =
	//l1-index of descriptor to write.
	//Bit shifting left by 20 bits gives the virtual base address of the MB to map.
	addr_t virt_transl_for_pmd = (addr_t) ((pmd - pgd_va) << MMU_L1_SECTION_SHIFT);

	if (desc == 0) {	//Unmap
		uint32_t linux_va = pmd[0] - phys_start + page_offset;
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA, linux_va);
		COP_WRITE(COP_SYSTEM, COP_BRANCH_PRED_INVAL_ALL, linux_va);
		dsb();
		isb();

		if (err = dmmu_unmap_L1_pageTable_entry(virt_transl_for_pmd)) {
			if (err != ERR_MMU_ENTRY_UNMAPPED) {	//Not already unmapped.
				printf("\n\thypercall_dyn_set_pmd2: Could not unmap L1 entry in set PMD0, err = %d\n", err);
				while (1);
			}
		}
		if (err = dmmu_unmap_L1_pageTable_entry(virt_transl_for_pmd + SECTION_SIZE)) {
			if (err != ERR_MMU_ENTRY_UNMAPPED) {	//Not already unmapped.
				printf("\n\thypercall_dyn_set_pmd3: Could not unmap L1 entry in set PMD1, err = %d\n", err);
				while (1);
			}
		}

#ifdef AGGRESSIVE_FLUSHING_HANDLERS
		COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, (uint32_t) pmd);
#endif

		/*We need to make the l2 page RW again so that
		 *OS can reuse the address */
		if (err = dmmu_l2_unmap_entry((uint32_t) l2pt_pa & L2_BASE_MASK, table2_idx + l2_idx)) {
			printf("\n\thypercall_dyn_set_pmd4: Could not unmap L2 entry in set PMD, err = %d\n", err);
			while (1);
		}
		if (err = dmmu_unmap_L2_pt(MMU_L2_SMALL_ADDR((uint32_t) * pmd))) {
//			printf("\n\thypercall_dyn_set_pmd5: Could not unmap L2 pt in set PMD, err = %d\n", err);
//			print_all_pointing_L1(MMU_L2_SMALL_ADDR((uint32_t) * pmd), 0xFFFFFFFF);
//			print_all_pointing_L2(MMU_L2_SMALL_ADDR((uint32_t) * pmd), 0xFFFFFFFF);
//			while (1);
		}

		if (err = L2_MAP((uint32_t) l2pt_pa & L2_BASE_MASK, table2_idx + l2_idx, MMU_L2_SMALL_ADDR((uint32_t) * pmd), l2_rw_attrs)) {
			printf("\n\thypercall_dyn_set_pmd6: Could not map L2 entry in set PMD, err = %d\n", err);
			while (1);
		}

		//COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, (uint32_t)&l2pt_va[l2_idx]);
		CacheDataInvalidateBuff((uint32_t) & l2pt_va[l2_idx], 4);
		/*Flush entry */
		dsb();
	} else {		//Map
		//L1-descriptor to write - physical start address of linux + virtual start address of linux =
		//virtual address of l2 page table that desc points to.
		uint32_t linux_va = desc - phys_start + page_offset;
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA, linux_va);
		COP_WRITE(COP_SYSTEM, COP_BRANCH_PRED_INVAL_ALL, linux_va);
		dsb();
		isb();

		/*Flush entry */
		//Virtual MB index to map to l2 page identified by l1-descriptor.
//		err = dmmu_l1_pt_map(virt_transl_for_pmd, MMU_L2_SMALL_ADDR(desc), attrs);
		err = dmmu_l1_pt_map(virt_transl_for_pmd, 0xFFFFFC00 & desc, attrs);
		if (err) {
		printf("\n\thypercall_dyn_set_pmd7: Could not map L1 entry in set PMD, err = %d\n", err);
			if (err = dmmu_unmap_L1_pageTable_entry(virt_transl_for_pmd)) {
				printf("\n\thypercall_dyn_set_pmd8: Could not unmap L1 entry in set PMD2, err = %d\n", err);
				while (1);
			}

//			if (err = dmmu_l1_pt_map(virt_transl_for_pmd, MMU_L2_SMALL_ADDR(desc), attrs)) {
			printf("HYPERVISOR: hypercall_map_block2: START.\n");
			err = dmmu_l1_pt_map(virt_transl_for_pmd, 0xFFFFFC00 & desc, attrs);
			printf("HYPERVISOR: hypercall_map_block2: END.\n");
			if (err) {
				printf("hypercall_dyn_set_pmd9: Could not map L1 PT in set PMD err = %d, virt_transl_for_pmd = %x, pmd = 0x%x, pgd_va = 0x%x, pmd - pgd_va = 0x%x\n", err, virt_transl_for_pmd, pmd, pgd_va, pmd - pgd_va);
				while (1);
			}
		}
//		err = dmmu_l1_pt_map(virt_transl_for_pmd + SECTION_SIZE, MMU_L2_SMALL_ADDR(desc) + 0x400, attrs);
		err = dmmu_l1_pt_map(virt_transl_for_pmd + SECTION_SIZE, (0xFFFFFC00 & desc) + 0x400, attrs);
		if (err) {
			if (err = dmmu_unmap_L1_pageTable_entry(virt_transl_for_pmd + SECTION_SIZE)) {
				printf("\n\thypercall_dyn_set_pmd10: Could not unmap L1 entry in set PMD3, err = %d\n", err);
				while (1);
			}

//			if (err = dmmu_l1_pt_map(virt_transl_for_pmd + SECTION_SIZE, MMU_L2_SMALL_ADDR(desc) + 0x400, attrs)) {
			printf("HYPERVISOR: hypercall_map_block4: START.\n");
			err = dmmu_l1_pt_map(virt_transl_for_pmd + SECTION_SIZE, (0xFFFFFC00 & desc) + 0x400, attrs);
			printf("HYPERVISOR: hypercall_map_block4: END.\n");
			if (err) {
				printf("hypercall_dyn_set_pmd11: Could not map L1 PT in set PMD err = %d, virt_transl_for_pmd = %x, pmd = 0x%x, pgd_va = 0x%x, pmd - pgd_va = 0x%x\n", err, virt_transl_for_pmd + SECTION_SIZE, pmd, pgd_va, pmd - pgd_va);
				while (1);
			}
		}
		/*Flush entry */
		CacheDataInvalidateBuff((uint32_t) pmd, 4);
		CacheDataInvalidateBuff((uint32_t) & l2pt_va[l2_idx], 4);
		dsb();

	}
	if (switch_back) {
		COP_WRITE(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, curr_pgd_pa);	// Set TTB0
		isb();
	}
	/*Flush entry */
	clean_and_invalidate_cache();
}

/* If the virtual address of a second-level page table entry is within
 * [vstart + psize, vstart + psize + 1MB), then Linux attempts to modify a
 * second-level page table, whose virtual address is unmapped.
 *
 * A virtual address pte_va ∈ [vstart + psize, vstart + psize + 1MB), with
 * offset = pte_va - (vstart + psize), addresses the second-level page table at
 * physical address pstart + psize and virtual address
 * curr_vm.config->reserved_va_for_pt_access_start + psize + offset, where
 * curr_vm.config->reserved_va_for_pt_access_start = 0xE800_0000.
 *
 * [0xE800_0000, 0xE800_0000 + 112MB + 1MB) -> [0x8100_0000, 0x8100_0000 + 112MB + 1MB) =
 * [0xE800_0000, 0xE800_0000 + 0x0700_0000 + 0x0010_0000) -> [0x8100_0000, 0x8100_0000 + 0x0700_0000 + 0x0010_0000) =
 * [0xE800_0000, 0xEF00_0000 + 0x0010_0000) -> [0x8100_0000, 0x8800_0000 + 0x0010_0000) =
 * [0xE800_0000, 0xEF10_0000) -> [0x8100_0000, 0x8810_0000)
 */
uint32_t find_l2pt_entry_va(uint32_t l2pt_linux_entry_va) {
	uint32_t psize = curr_vm->config->firmware->psize;
	uint32_t vstart = curr_vm->config->firmware->vstart;

	if (l2pt_linux_entry_va >= vstart + psize + SECTION_SIZE) {
		printf("Hypervisor find_l2pt_entry_va: Linux provides virtual address of second-level page table entry that is not among the second-level page tables following physical Linux memory.\n");
		while (1);
	}

	if (l2pt_linux_entry_va >= vstart + psize) {
		//Linux provides a virtual address to a second-level page table entry
		//that is not directly accessible through the given virtual address if
		//Linux has mapped something else from that address or not mapped that
		//address at all.
		uint32_t pte_offset = l2pt_linux_entry_va - (vstart + psize);
printf("find_l2pt_entry_va: Old va = 0x%x\n", l2pt_linux_entry_va);
		l2pt_linux_entry_va = ((uint32_t) curr_vm->config->reserved_va_for_pt_access_start) + psize + pte_offset;
printf("find_l2pt_entry_va: New va = 0x%x, desc = 0x%x\n", l2pt_linux_entry_va, *((uint32_t *) l2pt_linux_entry_va));
	}

	return l2pt_linux_entry_va;
}

/* va is the virtual address of the page table entry for linux pages
 * the physical pages are located 0x800 = 2048 above */
void hypercall_dyn_set_pte(addr_t * l2pt_linux_entry_va, uint32_t linux_pte, uint32_t phys_pte)
{
	uint32_t l1_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pa);
	uint32_t l1_va = l1_pa - curr_vm->config->firmware->pstart + curr_vm->config->firmware->vstart;

#ifdef DEBUG_MMU
	printf("Hypercall set PTE va:%x linux_pte:%x phys_pte:%x \n", l2pt_linux_entry_va, phys_pte, linux_pte);
#endif

	addr_t phys_start = curr_vm->config->firmware->pstart;
	uint32_t page_offset = curr_vm->guest_info.page_offset;
	uint32_t guest_size = curr_vm->config->firmware->psize;
	uint32_t l2pt_hw_entry_va = (uint32_t) ((addr_t) l2pt_linux_entry_va + 0x800);
	addr_t l2pt_hw_entry_pa = ((addr_t) l2pt_hw_entry_va - page_offset + phys_start);

	/*Security Checks */
	uint32_t pa = MMU_L2_SMALL_ADDR(phys_pte);

	/*Check virtual address */
	if (l2pt_hw_entry_va < page_offset || (uint32_t) l2pt_linux_entry_va > (uint32_t) (HAL_VIRT_START - sizeof(uint32_t))) {
		hyper_panic("Page table entry reside outside of allowed address space !\n", 1);
		printf("%s ErRor va:%x pgf:%x", __func__, l2pt_hw_entry_va, page_offset);
		while (1);
	}

	if (phys_pte != 0) {	/*If 0, then its a remove mapping */
		/*Check physical address */
		if (!(pa >= (phys_start) && pa < (phys_start + guest_size))) {
			printf("hypercall_dyn_set_pte0: Guest tries to map physical memory outside its region: PA = 0x%x\n", pa);
			while (1);
		}
	}

	/*Get index of physical L2PT */
	uint32_t entry_idx = ((addr_t) l2pt_hw_entry_va & 0xFFF) >> 2;
	/*Small page with CB on and RW */
	uint32_t attrs = phys_pte & 0xFFF;	/*Mask out address */
	uint32_t err;
	if (phys_pte != 0) {
		if (err = L2_MAP(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx, MMU_L1_PT_ADDR(phys_pte), attrs)) {
			if (err == ERR_MMU_PT_NOT_UNMAPPED) {
				/*So DMMU API does not allow changing attributes or remapping an entry if its not empty
				 *this is a workaround */
//printf("HYPERVISOR REMAPS l2pt_linux_entry_va = %x, l2pt_hw_entry_pa = %x, entry_idx = %x, physical level-2 page table base address %x\n", l2pt_linux_entry_va, l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx, MMU_L1_PT_ADDR(phys_pte));
				dmmu_l2_unmap_entry(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx);
				err = L2_MAP(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx, MMU_L1_PT_ADDR(phys_pte), attrs);
				if (err == ERR_MMU_NEW_L2_NOW_WRITABLE) {			//Tries to map itself (L2 page) as writable.
					attrs &= ~0x10;	//Clear write permission of new descriptor to the page table at l2pt_hw_entry_pa & L2_BASE_MASK.
					err = L2_MAP(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx, MMU_L1_PT_ADDR(phys_pte), attrs);
					if (err) {
						printf("Could not mark page as an l2 page table in set pte hypercall selfmap: err = %d\n", err);
						while (1);
					} else
						printf("Could mark page as an l2 page table after selfremap in set pte hypercall.\n");
				} else if (err == ERR_MMU_PH_BLOCK_NOT_WRITABLE) {	//Tries to map an L2 page table as writable.
					attrs &= ~0x10;									//Clear write permission of new descriptor.
					err = L2_MAP(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx, MMU_L1_PT_ADDR(phys_pte), attrs);
					if (err) {
						printf("Could not mark page as an l2 page table in set pte hypercall when pointing to L2 page: err = %d\n", err);
						while (1);
					} else
						printf("Could mark page as an l2 page table after remap in set pte hypercall.\n");
				} else if (err) {
					printf("Could not mark page as an l2 page table in set pte hypercall0: err = %d\n", err);
					printf("Could not mark page as an l2 page table in set pte hypercall0: l2pt_hw_entry_pa & L2_BASE_MASK = 0x%x\n", l2pt_hw_entry_pa & L2_BASE_MASK);
					printf("Could not mark page as an l2 page table in set pte hypercall0: MMU_L1_PT_ADDR(phys_pte) = 0x%x\n", MMU_L1_PT_ADDR(phys_pte));
					printf("Could not mark page as an l2 page table in set pte hypercall0: attrs = 0x%x\n", attrs);
					while (1);
				}
			} else if (err == ERR_MMU_IS_NOT_L2_PT) {
				err = dmmu_create_L2_pt(l2pt_hw_entry_pa & L2_BASE_MASK);	//Mark identified L2-page table (from l1-entry) as L2.
				if (err == ERR_MMU_REFERENCED) {
					invalidate_l2_entries_with_invalid_aps(l2pt_hw_entry_pa & L2_BASE_MASK);
					remove_aps_l1(l2pt_hw_entry_pa & L2_BASE_MASK);
					err = dmmu_create_L2_pt(l2pt_hw_entry_pa & L2_BASE_MASK);	//Mark identified L2-page table (from l1-entry) as L2.
					if (err) {
						printf("\n\tCould not create l2 page table set pte hypercall1: err = %d with l2pt_hw_entry_pa = 0x%x\n", err, l2pt_hw_entry_pa & L2_BASE_MASK);
						print_all_pointing_L2(l2pt_hw_entry_pa & L2_BASE_MASK, 0xFFFFFFFF);
						while (1);
					}
				} else if (err != SUCCESS_MMU && err != ERR_MMU_ALREADY_L2_PT) {	//Not success and not already marked as L2.
					printf("\n\tCould not mark page as an l2 page table in set pte hypercall2: err = %d, l2pt_hw_entry_pa & L2_BASE_MASK = 0x%x\n", err, l2pt_hw_entry_pa & L2_BASE_MASK);
					while (1);
				}

				err = L2_MAP(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx, MMU_L1_PT_ADDR(phys_pte), attrs);
				if (err == ERR_MMU_PT_NOT_UNMAPPED) {
					err = dmmu_l2_unmap_entry(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx);
					if (err) {
						printf("Could not unmap entry 0x%x of l2 page table at 0x%x in set pte hypercall3: err = %d\n", entry_idx, l2pt_hw_entry_pa & L2_BASE_MASK, err);
						while (1);
					}
					err = L2_MAP(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx, MMU_L1_PT_ADDR(phys_pte), attrs);
					if (err) {
						printf("Could not set entry %d at va = 0x%x - 0x800 = 0x%x of l2 page table at 0x%x in set pte hypercall4: err = %d, pc = 0x%x\n", entry_idx, l2pt_linux_entry_va, l2pt_hw_entry_va, l2pt_hw_entry_pa & L2_BASE_MASK, err, curr_vm->current_mode_state->ctx.pc);
						while (1);
					}
				} else if (err) {
					printf("\n\tCould not map page as an l2 page table in set pte hypercall5: err = %d\n", err);
					while (1);
				}
			} else {
				printf("\n\tCould not map l2 entry in set pte hypercall6: err = %d\n", err);
				while (1);
			}
		}
	} else {
		/*Unmap */
		if (err = dmmu_l2_unmap_entry(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx)) {
//			uint32_t l2_type = get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(l2pt_hw_entry_pa & L2_BASE_MASK))->type;
			if (err == ERR_MMU_IS_NOT_L2_PT /*&& l2_type == PAGE_INFO_TYPE_DATA*/) {
				err = dmmu_create_L2_pt(l2pt_hw_entry_pa & L2_BASE_MASK);	//Mark identified L2-page table (from l1-entry) as L2.
				if (err == ERR_MMU_REFERENCED) {
					invalidate_l2_entries_with_invalid_aps(l2pt_hw_entry_pa & L2_BASE_MASK);
					remove_aps_l1(l2pt_hw_entry_pa & L2_BASE_MASK);
					err = dmmu_create_L2_pt(l2pt_hw_entry_pa & L2_BASE_MASK);	//Mark identified L2-page table (from l1-entry) as L2.
					if (err) {
						printf("\n\tCould not create l2 page table set pte hypercall7: err = %d with l2pt_hw_entry_pa = 0x%x\n", err, l2pt_hw_entry_pa & L2_BASE_MASK);
						print_all_pointing_L2(l2pt_hw_entry_pa & L2_BASE_MASK, 0xFFFFFFFF);
						while (1);
					}
				} else if (err != SUCCESS_MMU && err != ERR_MMU_ALREADY_L2_PT) {	//Not success and not already marked as L2.
					printf("\n\tCould not mark page as an l2 page table in set pte hypercall8: err = %d, l2pt_hw_entry_pa & L2_BASE_MASK = 0x%x\n", err, l2pt_hw_entry_pa & L2_BASE_MASK);
					while (1);
				}
				err = dmmu_l2_unmap_entry(l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx);
				if (err) {
					printf("\n\tCould not map page as an l2 page table in set pte hypercall9: err = %d\n", err);
					while (1);
				}
			} else if (err) {
				printf("\n\tCould not unmap l2 entry in set pte hypercall10: err = %d\n", err);
				while (1);
			}
		}
	}

	/*Do we need to use the DMMU API to set Linux pages? */
	*l2pt_linux_entry_va = linux_pte;

	COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, l2pt_hw_entry_va);
	clean_and_invalidate_cache();
}












/******************************************************************************
 *****************************Linux 5.15.13 additions**************************
 ******************************************************************************/
extern uint32_t *slpt_va;

void print_specific_L2(void) {
	uint32_t pa = 0x82DE0000;
	uint32_t mask = 0xFFFFFFFF;
	uint32_t ph_block_pg = PA_TO_PH_BLOCK(pa);
	dmmu_entry_t *bft_entry_pg = get_bft_entry_by_block_idx(ph_block_pg);

	uint32_t i = 0;
	uint32_t l2_idx;
	uint32_t number_of_l2 = 0;

	for (i = 0; i < (1 << 20); i += 1) {
		uint32_t pt_mask = 0xfffff000 & mask;
		dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(i);

		if (bft_entry->type != PAGE_INFO_TYPE_L2PT)
			continue;

		printf("   checking block %d\n", i);
		uint32_t l2_desc_pa_add = L2_DESC_PA(START_PA_OF_BLOCK(i), 0);
		uint32_t va_to_use = mmu_guest_pa_to_va(l2_desc_pa_add, curr_vm->config);
			
		if (!guest_pa_range_checker(START_PA_OF_BLOCK(i), PAGE_SIZE)) {
			printf("   skipping block outside guest memory in 0x%x\n", START_PA_OF_BLOCK(i));
			uint32_t pa = START_PA_OF_BLOCK(i);
			uint32_t slpt_pa = GET_PHYS(slpt_va);
			uint32_t slpt_pa_end = slpt_pa + 0x8000;
			if (!((pa >= slpt_pa) && (pa < slpt_pa_end)))
				continue;
			printf("   Internal hypervisor memory\n");
			va_to_use = ((uint32_t)slpt_va) + (pa - slpt_pa);
		}

		for (l2_idx = 512; l2_idx < 1024; l2_idx += 1) {
			uint32_t l2_desc_va_add = va_to_use + l2_idx*4;
			uint32_t l2_desc = *((uint32_t *) l2_desc_va_add);
			uint32_t l2_type = l2_desc & DESC_TYPE_MASK;

			if ((l2_type == 2) || (l2_type == 3)) {
				l2_small_t *pg_desc = (l2_small_t *) (&l2_desc);
				uint32_t l2_pointed_pa_add = START_PA_OF_SPT(pg_desc);
				uint32_t ap = GET_L2_AP(pg_desc);

				if ((l2_pointed_pa_add & pt_mask) ==
				    (pa & pt_mask)) {
					printf
					    ("   The L2 in 0x%x (index %d) points to 0x%x ap=%d xn=%d\n",
					     START_PA_OF_BLOCK(i), l2_idx, pa, ap, pg_desc->xn);
					if (ap == 3) {
						number_of_l2 += 1;
					}
				}
			}
		}
	}

	printf("   number of L2s = %d\n", number_of_l2);
	printf("   block ref cnt = %d\n", bft_entry_pg->refcnt);
	printf("   block x-ref cnt = %d\n", bft_entry_pg->x_refcnt);

	uint32_t l1_pt_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
	uint32_t l1_pt_va = mmu_guest_pa_to_va(l1_pt_pa, curr_vm->config);	//l1_pt_va = 0xC0004000
	uint32_t l1i;
	for (l1i = 0; l1i < (HAL_VIRT_START >> 20); l1i = l1i + 1) {
		uint32_t l1e = *((uint32_t *) (l1_pt_va + l1i*4));
		if ((l1e & 0x3) == 0x1 && (l1e & 0xFFFFF000) == 0x8800E000) {
			printf("IN MAPPING AT INDEX 0x%x\n", l1i);
		}
	}
}





void remove_l1_mappings(uint32_t pa) {
	if (get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(pa))->type == PAGE_INFO_TYPE_L2PT) {
		uint32_t err = dmmu_unmap_L2_pt(pa & 0xFFFFF000);
		if (err) {
			printf("remove_l1_mappings: Error = 0x%x.\n", err);
			while (1);
		}// else
//			printf("remove_l1_mappings: Removed mapping to l2 page at 0x%x.\n", pa);
	} else {
		printf("remove_l1_mappings: Not L2 page type.\n");
		while (1);
	}

//	print_all_pointing_L1(0x82DE0000, 0xFFFFF000);
//	print_all_pointing_L1(pa, 0xFFFFF000);
}

BOOL emulate_write(uint32_t va, uint32_t fault_instruction_va) {
	//We read from the active L1 who is mapping this virtual address
	uint32_t l1_pt_pa;
	uint32_t l1i;
	uint32_t l1e_pa, l1e_va, l1e, l1_type;
	uint32_t page_pa;
	uint32_t l2_pt_pa;
	uint32_t l2i;

	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
	l1i = va >> 20;
	l1e_pa = (l1_pt_pa & 0xFFFFC000) | (l1i << 2);
	l1e_va = mmu_guest_pa_to_va(l1e_pa, curr_vm->config);
	l1e = *((uint32_t *) l1e_va);
	l1_type = l1e & 0x3;

	// The address is unmapped (0)
	// The address is mapped by an unkwown mechanism (3)
	// The address is mapped by a section (2)
	// With the new mechanism the kernel memory should be never mapped by a section
	if (l1_type == 0 || l1_type == 3 || l1_type == 2)
		return FALSE;

	// The address is mapped by a PT, l1_type == 1
	l2_pt_pa = l1e & 0xFFFFFC00;
	l2i = (0x000FF000 & va) >> 12;

	uint32_t l2e_pa = l2_pt_pa + l2i*4;
	uint32_t l2e_va = mmu_guest_pa_to_va(l2e_pa, (curr_vm->config));
	uint32_t l2e = *((uint32_t *) l2e_va);

	// Unmapped: nothing to emulate
	if((l2e & 0x3) == 0)
		return FALSE;

//	printf("AP = 0x%x\n", ((l2e & (0x1 << 9)) >> 7) | ((l2e & (0x3 << 4)) >> 4));

	l2i = l2i + ((l2_pt_pa - (l2_pt_pa & 0xFFFFF000)) >> 10)*256;	//Adds 512 or 768 depending on whether l2_pt_pa is in the second or third kB of the 4kB page.
	uint32_t err = dmmu_l2_unmap_entry(l2_pt_pa & 0xFFFFF000, l2i);
	if (err) {
		printf("emulate_write1: Could not unmap l2 entry.\n");
		while (1);
	}
	page_pa = l2e & 0xFFFFF000;
	uint32_t small_attrs = (l2e & ~(0x1 << 9)) | (0x3 << 4);	//Make writable in PL0.
//uint32_t l2e_new = CREATE_L2_DESC(page_pa, small_attrs);
//	printf("NEW AP = 0x%x\n", ((l2e_new & (0x1 << 9)) >> 7) | ((l2e_new & (0x3 << 4)) >> 4));
	err = dmmu_l2_map_entry(l2_pt_pa & 0xFFFFF000, l2i, page_pa, small_attrs);
	if (err == ERR_MMU_PH_BLOCK_NOT_WRITABLE) {
		dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(page_pa));
		if (bft_entry->type == PAGE_INFO_TYPE_L2PT) {
//			printf("emulate_write2: Removes l1 mapping to 0x%x since it must be"
//					" written by the instruction at 0x%x and is currently"
//					" classified as an L2 page.\n", page_pa, fault_instruction_va);
			remove_l1_mappings(page_pa);
//			printf("emulate_write3: Removed l1 mapping to 0x%x since it must be"
//					" written by the instruction at 0x%x and is currently"
//					" classified as an L2 page.\n", page_pa, fault_instruction_va);
			err = dmmu_l2_map_entry(l2_pt_pa & 0xFFFFF000, l2i, page_pa, small_attrs);
			if (err) {
				printf("emulate_write2: Could not map entry 0x%x of l2 page table at 0x%x to page at 0x%x.\n", l2i, l2_pt_pa & 0xFFFFF000, page_pa);
				while (1);
			}
		} else if (bft_entry->type == PAGE_INFO_TYPE_DATA) {
			printf("emulate_write3: Mapping page at 0x%x, of type data, not possible.\n", page_pa);
			while (1);
		} else if (bft_entry->type == PAGE_INFO_TYPE_L1PT) {
			err = dmmu_unmap_L1_pt(page_pa & 0xFFFFC000);	//16 kB aligned.
			if (err) {
				printf("emulate_write4: Could not remove l1 page table at 0x%x, due to err = %d, pc = 0x%x.\n", page_pa, err, fault_instruction_va);
				while (1);
			}
			err = dmmu_l2_map_entry(l2_pt_pa & 0xFFFFF000, l2i, page_pa, small_attrs);
			if (err) {
				printf("emulate_write5: Could not remap l2 page table at 0x%x.\n", page_pa);
				while (1);
			}
		} else if (bft_entry->type == PAGE_INFO_TYPE_INVALID) {
			printf("emulate_write6: Mapping page at 0x%x, of type invalid, not possible.\n", page_pa);
			while (1);
		} else {
			printf("emulate_write7: Mapping page at 0x%x, of incorrect encoding, not possible.\n", page_pa);
			while (1);
		}

	} else if (err) {
		printf("emulate_write8: Could not map l2 entry: l2_pt_pa = 0x%x,"
				" l2i = 0x%x, page_pa = 0x%x, va = 0x%x,"
				" fault_instruction_va = 0x%x.\n", l2_pt_pa, l2i, page_pa, va, fault_instruction_va);
		while (1);
	}

	uint32_t mva;
	for (mva = (va & 0xFFFFF000); mva < (0xFFFFF000 & va) + 0x1000; mva = mva + 4) {//APs of 1 4kB page are changed.
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA, mva);
		COP_WRITE(COP_SYSTEM, COP_BRANCH_PRED_INVAL_ALL, mva);
	}

	dsb();
	isb();
	hypercall_dcache_clean_area(l2e_va, 0x1000);

	return TRUE;
}






uint32_t invalidate_l2_entries_with_invalid_aps(uint32_t l2_pt_pa) {
	uint32_t l2i;
	for (l2i = 512; l2i < 1024; l2i++) {
		uint32_t l2e_pa = L2_DESC_PA(l2_pt_pa, l2i);
		uint32_t l2e_va = mmu_guest_pa_to_va(l2e_pa, curr_vm->config);
		uint32_t l2e = *((uint32_t *) l2e_va);
		uint32_t l2_type = l2e & DESC_TYPE_MASK;
		uint32_t current_check = l2Desc_validityChecker_dispatcher(l2_type, l2e, l2_pt_pa);
		if (current_check == ERR_MMU_AP_UNSUPPORTED) {
//			printf("invalidate_l2_entries_with_invalid_aps: Invalidates entry"
//					" with invalid AP, l2_pt_pa = 0x%x, l2i = 0x%x, l2e = 0x%x\n",
//					 l2_pt_pa, l2i, l2e);
			*((uint32_t *) l2e_va) = l2e & 0xFFFFFFFC;
		} else if (current_check == ERR_MMU_L2_UNSUPPORTED_DESC_TYPE) {
//			printf("invalidate_l2_entries_with_invalid_aps: Invalidates entry"
//					" with invalid type, l2_pt_pa = 0x%x, l2i = 0x%x, l2e = 0x%x\n",
//					 l2_pt_pa, l2i, l2e);
			*((uint32_t *) l2e_va) = l2e & 0xFFFFFFFC;
		} else if (current_check == ERR_MMU_OUT_OF_RANGE_PA) {
//			printf("invalidate_l2_entries_with_invalid_aps: Invalidates entry"
//					" with l2 descriptor addressing a page outside guest memory,"
//					" l2_pt_pa = 0x%x, l2i = 0x%x, pa of addressed page = 0x%x\n",
//					 l2_pt_pa, l2i, l2e & 0xFFFFF000);
			*((uint32_t *) l2e_va) = l2e & 0xFFFFFFFC;
		} else if (current_check != SUCCESS_MMU) {
			printf("invalidate_l2_entries_with_invalid_aps: Invalid entry with"
					" valid AP, err = %d\n", current_check);
			while (1);
		}
	}
//	printf("invalidate_l2_entries_with_invalid_aps returns.\n");
}

void find_mapping_l2(uint32_t l2_pt_pa, uint32_t pa, uint32_t l1i) {
	uint32_t l1_pt_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
	uint32_t l1_pt_va = mmu_guest_pa_to_va(l1_pt_pa, curr_vm->config);	//l1_pt_va = 0xC0004000
	uint32_t l2_pt_va = mmu_guest_pa_to_va(l2_pt_pa, curr_vm->config);

	uint32_t l2i;
	for (l2i = 0; l2i < 256; l2i = l2i + 1) {
		uint32_t l2e = *((uint32_t *) (l2_pt_va + l2i*4));
		if ((l2e & 0x2) == 0x2 && (l2e & 0xFFFFF000) == (pa & 0xFFFFF000)) {
			printf("L1 entry with index 0x%x and virtual address 0x%x, points"
					" to L2 page table at virtual address 0x%x (pa = 0x%x) with"
					" index 0x%x, resulting in a map to 0x%x\n",
					 l1i, (l1i << 2) + l1_pt_va, l2_pt_va, l2_pt_pa, l2i, pa);
		}
	}
}

void find_mapping_l1(uint32_t pa) {
	uint32_t l1_pt_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
	uint32_t l1_pt_va = mmu_guest_pa_to_va(l1_pt_pa, curr_vm->config);	//l1_pt_va = 0xC0004000
	uint32_t l1i;

	for (l1i = 0; l1i < (HAL_VIRT_START >> 20); l1i = l1i + 1) {
		uint32_t l1e = *((uint32_t *) (l1_pt_va + l1i*4));
		if ((l1e & 0x3) == 0x1) {
			uint32_t l2_pt_pa = l1e & 0xFFFFFC00;
			find_mapping_l2(l2_pt_pa, pa, l1i);
		}
	}
}

void invalidate_vas_mapped_by_l2_pt(uint32_t l2_pt_pa, uint32_t l2i) {
	uint32_t l1i, l1_pt_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
	uint32_t l1_pt_va = mmu_guest_pa_to_va(l1_pt_pa, curr_vm->config);	//l1_pt_va = 0xC0004000

	for (l1i = 0; l1i < (HAL_VIRT_START >> 20); l1i++) {
		uint32_t l1e = *((uint32_t *) (l1_pt_va + l1i*4));
		if ((l1e & 0x3) == 0x1 && (l1e & 0xFFFFF000) == l2_pt_pa) {
			uint32_t addr;
			for (addr = (l1i << 20) + (l2i << 12); addr < (l1i << 20) + ((l2i + 2) << 12); addr = addr + 4) {	//l2i + 2 since 2 page tables of 256 entries each are to be invalidated.
				//Cleans all virtual addresses mapped by the 2 l2 page tables at l2_pt_pa: 512*4kB = 2MB.
				COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA, addr);
				COP_WRITE(COP_SYSTEM, COP_BRANCH_PRED_INVAL_ALL, addr);
			}
		}
	}
}

void remove_w_l2(uint32_t l2_pt_pa, uint32_t l2i, uint32_t l2e) {
	l2i = ((l2_pt_pa - (l2_pt_pa & 0xFFFFF000)) >> 10)*256 + l2i;	//Adds the index offset 512 or 768 depending on whether l2_pt_pa is the third or fourth kB of the 4k page containing it.
	l2_pt_pa = l2_pt_pa & 0xFFFFF000;

	uint32_t err = dmmu_l2_unmap_entry(l2_pt_pa, l2i);
	if (err) {
		printf("remove_w_l2: Could not unmap l2 entry: l2_pt_pa = 0x%x, l2i = 0x%x\n", l2_pt_pa, l2i);
		while (1);
	}

	//Extract attributes and clear AP[0] to make read-only in PL0.
	uint32_t small_attrs = (l2e & 0x00000FFD & ~(0x200 | 0x10)) | 0x20;
	uint32_t page_pa = l2e & 0xFFFFF000;
	err = dmmu_l2_map_entry(l2_pt_pa, l2i, page_pa, small_attrs);
	if (err) {
		printf("remove_w_l2: Could not map l2 entry: l2_pt_pa = 0x%x,"
				" page_pa = 0x%x, l2i = 0x%x, small_attrs = 0x%x\n",
				 l2_pt_pa, page_pa, l2i, small_attrs);
		while (1);
	}
/*	//DONE BY OTHER hyp_dmmu functions.
	invalidate_vas_mapped_by_l2_pt(l2_pt_pa, l2i);
	dsb();
	isb();
	uint32_t l2_pt_va = mmu_guest_pa_to_va(l2_pt_pa, curr_vm->config);
	uint32_t l2e_va = l2_pt_va + l2i*4;
	hypercall_dcache_clean_area(l2e_va, 0x1000);	//Clean 4kB = size of one page.
*/
}
/*
void remove_aps_l2(uint32_t l2_pt_pa, uint32_t pa, uint32_t l1i) {
	uint32_t l2_pt_va = mmu_guest_pa_to_va(l2_pt_pa, curr_vm->config);
	uint32_t l2i;
if (l2_pt_pa & 0xFFFFFC00 == 0x82DE0000) printf("REMOVE_APS_L2: l2_pt_pa = 0x%x, pa = 0x%x, l1i = 0x%x", l2_pt_pa, pa, l1i);
	for (l2i = 0; l2i < 512; l2i = l2i + 1) {
		uint32_t l2e_va = l2_pt_va + l2i*4;
		uint32_t l2e = *((uint32_t *) l2e_va);
		if ((l2e & 0x2) == 0x2 && (l2e & 0xFFFFF000) == (pa & 0xFFFFF000)) {
			uint32_t l1_pt_pa;
			COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
			uint32_t l1_pt_va = mmu_guest_pa_to_va(l1_pt_pa, curr_vm->config);	//l1_base_va = 0xC0004000
			printf("Removes mapping: L1 entry with index 0x%x and virtual"
					" address 0x%x, points to L2 page table at virtual address"
					" 0x%x (pa = 0x%x) with index 0x%x, resulting in a map to"
					" 0x%x\n", l1i, (l1i << 2) + l1_pt_va, l2_pt_va, l2_pt_pa, l2i, pa);
			remove_w_l2(l2_pt_pa, l2i, l2e);
			printf("Removed mapping: L1 entry with index 0x%x and virtual"
					" address 0x%x, points to L2 page table at virtual address"
					" 0x%x (pa = 0x%x) with index 0x%x, resulting in a map to"
					" 0x%x\n", l1i, (l1i << 2) + l1_pt_va, l2_pt_va, l2_pt_pa, l2i, pa);
		}
	}
}
*/

void remove_aps_l2(uint32_t l2_pt_pa, uint32_t pa, uint32_t l1i) {
	uint32_t l2_pt_va = mmu_guest_pa_to_va(l2_pt_pa, curr_vm->config);
	uint32_t l2i;
//if (l2_pt_pa & 0xFFFFFC00 == 0x82DE0000) printf("REMOVE_APS_L2: l2_pt_pa = 0x%x, pa = 0x%x, l1i = 0x%x", l2_pt_pa, pa, l1i);
	for (l2i = 0; l2i < 256; l2i = l2i + 1) {
		uint32_t l2e_va = l2_pt_va + l2i*4;
		uint32_t l2e = *((uint32_t *) l2e_va);
		if ((l2e & 0x2) == 0x2 && (l2e & 0xFFFFF000) == (pa & 0xFFFFF000)) {
			uint32_t l1_pt_pa;
			COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
			uint32_t l1_pt_va = mmu_guest_pa_to_va(l1_pt_pa, curr_vm->config);	//l1_base_va = 0xC0004000
			printf("Removes writable mapping: L1 entry with index 0x%x and virtual"
					" address 0x%x, points to L2 page table at virtual address 0x%x"
					" (pa = 0x%x) with index 0x%x, resulting in a map to 0x%x\n",
					 l1i, (l1i << 2) + l1_pt_va, l2_pt_va, l2_pt_pa, l2i, pa);

			remove_w_l2(l2_pt_pa, l2i, l2e);

			printf("Removed writable mapping: L1 entry with index 0x%x and virtual"
					" address 0x%x, points to L2 page table at virtual address 0x%x"
					" (pa = 0x%x) with index 0x%x, resulting in a map to 0x%x\n",
					 l1i, (l1i << 2) + l1_pt_va, l2_pt_va, l2_pt_pa, l2i, pa);
		}
	}
}

void remove_aps_l1(uint32_t pa) {
	uint32_t l1i, l1_pt_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
	uint32_t l1_pt_va = mmu_guest_pa_to_va(l1_pt_pa, curr_vm->config);	//l1_pt_va = 0xC0004000

	//Do not remove APs of page tables to hypervisor memory.
	for (l1i = 0; l1i < (HAL_VIRT_START >> 20); l1i = l1i + 1) {	//L1 indexes up to HV memory, 2MB at a time.
		uint32_t l1e = *((uint32_t *) (l1_pt_va + l1i*4));
		if ((l1e & 0x3) == 0x1) {
			uint32_t l2_pt_pa = l1e & 0xFFFFFC00;
			//Page tables for hypervisor to access Linux not forced to have same layout as Linux.
			remove_aps_l2(l2_pt_pa, pa, l1i);
		}
	}

//	remove_aps_boot_l2s(pa);	//Remove references to pa from the L2 page tables in boot.
}

//Gives the physical address of the 1kB level-2 page table with 256 entries that
//maps to @pa, as assigned by linux_pt_get_empty_l2. linux_l2_index_p: 4kB
//aligned or 4kB aligned + 1kB. For every 2MBs, linux_l2_index_p is incremented
//by 4.
/* THIS IS OLD VERSION BEFORE CHANGING linux_init.c:linux_init_dmmu to initialize page tables in correct order.
uint32_t pa_to_l2_base_pa(addr_t pa) {
	addr_t guest_pstart = curr_vm->config->firmware->pstart;

	if ((pa & 0xFFF00000) == guest_pstart)// {			//@pa in 1st MB of memory, last index.
		pa = guest_pstart + curr_vm->config->firmware->psize;
					/*	This was commented out before changing linux_init.c:linux_init_dmmu.
							addr_t guest_psize = curr_vm->config->firmware->psize;
							addr_t first_offset = SECTION_SIZE;
							addr_t last_offset = (guest_psize & 0xFFF00000) - SECTION_SIZE;
							addr_t number_of_sections = ((last_offset - first_offset) >> 20) + 1;
							uint32_t number_of_2mb_sections = number_of_sections >> 1;
							addr_t number_of_1kB_page_tables = number_of_2mb_sections * 4;	//4 1kB page tables per 2MB.
							if ((number_of_sections & 0x1) == 0x1)			//Odd number of sections require an additional 1kB page table.
								number_of_1kB_page_tables++;

							addr_t index = number_of_1kB_page_tables * 0x400;
							addr_t l2_page_table_base_pa = guest_pstart + curr_vm->config->pa_initial_l2_offset;
							addr_t l2_base_add = l2_page_table_base_pa + index;
							return l2_base_add;
						} else {											//@pa is not 1st MB of memory.
					*/
/*
	addr_t pa_offset = pa - SECTION_SIZE - guest_pstart;	//2nd MB has index 0, etc.
	addr_t mb2_offset = pa_offset >> 21;
	addr_t linux_l2_index_p = mb2_offset*4;			//4 1kB page tables per 2MB.
	if ((pa_offset & 0x00100000) == 0x00100000)		//Second MB in 2MB: Increment by
		linux_l2_index_p = linux_l2_index_p + 1;	//1 to get next 1kB page table.
	addr_t index = linux_l2_index_p * 0x400;		//Byte index to level-2 page table by multiplying with 1024.
	uint32_t pa_l2_pt = guest_pstart + curr_vm->config->pa_initial_l2_offset;
	uint32_t l2_base_add = pa_l2_pt + index + 2048;	//Add 2048 to skip the Linux meta data and get to the hardware page table entries.
	return l2_base_add;
//	}
}
*/
uint32_t pa_to_l2_base_pa(addr_t pa) {
	uint32_t guest_pstart = curr_vm->config->firmware->pstart;
	uint32_t pa_offset = pa - guest_pstart;
	uint32_t mb2_offset = pa_offset >> 21;			//2MB offset index.
	uint32_t linux_l2_index_p = mb2_offset*4;			//4 1kB page tables per 2MB.
//	if ((pa_offset & 0x00100000) == 0x00100000)		//Second MB in 2MB: Increment by
//		linux_l2_index_p = linux_l2_index_p + 1;	//1 to get next 1kB page table.
//kanske ska vara + 3 om andra MB och + 2 om första MB.

	linux_l2_index_p = (pa_offset & 0x00100000) == 0x00100000 ? linux_l2_index_p + 3 : linux_l2_index_p + 2;

	uint32_t index = linux_l2_index_p*1024;	//Multiply 1024 to get byte index to L2 page table.
	uint32_t pa_l2_pt = guest_pstart + curr_vm->config->pa_initial_l2_offset;
	uint32_t l2_base_add = pa_l2_pt + index;
	return l2_base_add;
}

//Given kernel_sec_start and kernel_sec_end, sets up page tables from
//OxC000_0000 to kernel_sec_start, with 1MB section granularity, covering up to
//but not including kernel_sec_end, flushing/invalidation cache/tlb.
//PAGE_OFFSET is the first virtual address of Linux, normally 0xC000_0000.
void linux_boot_virtual_map_section(uint32_t PAGE_OFFSET, uint32_t kernel_sec_start, uint32_t kernel_sec_end) {
////////////////////////////////////////////////////////////////////////////////
////This line causes all of Linux memory to be mapped as sections. This enables/
////Linux in arch/arm/mm/mmu.c:map_lowmem to write zeros to pages, via virtual//
////addresses, allocated to become L2-page tables, so that Linux can allocate///
////and use L2-page tables instead of sections./////////////////////////////////
//	kernel_sec_end = kernel_sec_start + curr_vm->config->firmware->psize;///////
//	printf("Hypercall 1: Adjusts initial boot virtual Linux map: end va = 0x%x, end pa = 0x%x\n", PAGE_OFFSET + curr_vm->config->firmware->psize, kernel_sec_end);
////////////////////////////////////////////////////////////////////////////////
	if (kernel_sec_start != curr_vm->config->firmware->pstart) {
		printf("HYPERVISOR: linux_boot_virtual_map_section: Linux start as\n");
		printf("computed by Linux is not consistent with Linux start as\n");
		printf("configured in hypervisor.\n");
		while (1);
	} else if (PAGE_OFFSET != curr_vm->guest_info.page_offset) {
		printf("HYPERVISOR: linux_boot_virtual_map_section: Linux virtual start as\n");
		printf("computed by Linux is not consistent with Linux start as\n");
		printf("configured in hypervisor.\n");
		while (1);
	} else if (kernel_sec_end - kernel_sec_start > curr_vm->config->firmware->psize) {
		printf("HYPERVISOR: linux_boot_virtual_map_section: Linux size as\n");
		printf("computed by Linux is not consistent with Linux start as\n");
		printf("configured in hypervisor.\n");
		while (1);
	}

	uint32_t page_attrs = MMU_L1_TYPE_PT | (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
	addr_t table2_pa;
	addr_t vstart = PAGE_OFFSET;	//0xC0000000;
	addr_t number_of_bytes = kernel_sec_end - kernel_sec_start;
	uint32_t offset;
	for (offset = 0; offset < number_of_bytes; offset += SECTION_SIZE) {
		table2_pa = pa_to_l2_base_pa(kernel_sec_start + offset);
		dmmu_l1_pt_map(vstart + offset, table2_pa, page_attrs);
	}

	//Complete memory accesses before invalidating/flushing caches.
	//BPIALL?????????
	dsb();
	isb();
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);	//TLB
	mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback
}

//Maps the DTB at physical address @fdt_base_pa to virtual address @fdt_base_va,
//by means of 2 MBs.
/*
void linux_boot_virtual_map_fdt(uint32_t fdt_base_pa, uint32_t fdt_base_va) {
	addr_t guest_pstart = curr_vm->config->firmware->pstart;
	addr_t fdt_pstart = fdt_base_pa & 0xFFF00000;	//1MB aligned.
	addr_t fdt_vstart = fdt_base_va & 0xFFF00000;	//1MB aligned.
	addr_t fdt_psize = 2*0x00100000;				//2MB. Linux reserves 2MB for DTB.

	addr_t l2_base_add = pa_to_l2_base_pa(fdt_pstart);
	uint32_t page_attrs = MMU_L1_TYPE_PT | (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
	dmmu_l1_pt_map(fdt_vstart, l2_base_add, page_attrs);

	//Complete memory accesses before invalidating/flushing caches.
	//BPIALL?????????
	dsb();
	isb();
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);	//TLB
	mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback
}
*/
void linux_boot_virtual_map_fdt(uint32_t fdt_base_pa, uint32_t fdt_base_va) {
	if (fdt_base_va > fdt_base_va + 2*SECTION_SIZE ||
		((fdt_base_va + 2*SECTION_SIZE) & 0xFFF00000) >= HAL_VIRT_START) {
		printf("HYPERVISOR: linux_boot_virtual_map_fdt: Maps hypervisor pages."
				" Inclusive start address = 0x%x, exclusive end address = 0x%x;"
				" Hypervisor start address = 0x%x.\n",
				 fdt_base_va, fdt_base_va + 2*SECTION_SIZE, HAL_VIRT_START);
		while (1);
	}

//	addr_t guest_pstart = curr_vm->config->firmware->pstart;
	addr_t fdt_pstart = fdt_base_pa & 0xFFF00000;	//1MB aligned.
	addr_t fdt_vstart = fdt_base_va & 0xFFF00000;	//1MB aligned.
//	addr_t fdt_psize = 2*0x00100000;				//2MB. Linux reserves 2MB for DTB.

	uint32_t page_attrs = MMU_L1_TYPE_PT | (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
	addr_t l2_base_add1 = pa_to_l2_base_pa(fdt_pstart);	//First MB.
	addr_t l2_base_add2 = pa_to_l2_base_pa(fdt_pstart + SECTION_SIZE);	//Second MB.
	dmmu_l1_pt_map(fdt_vstart, l2_base_add1, page_attrs);
	dmmu_l1_pt_map(fdt_vstart + SECTION_SIZE, l2_base_add2, page_attrs);

	//Complete memory accesses before invalidating/flushing caches.
	//BPIALL?????????
	dsb();
	isb();
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);	//TLB
	mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback
}

//Clears page table entries mapping on a 1MB section granularity:
//[start_pa, end_pa) and [start_va, end_va)
//where end_pa - start_pa = end_va - start_va and
//((end_pa >> 20) + 1) - (start_pa >> 20) = number_of_sections.
void linux_clear_virtual_map_section(uint32_t start_va, uint32_t end_va) {
	if ((end_va & 0xFFF00000) > HAL_VIRT_START) {
		printf("HYPERVISOR: linux_clear_virtual_map_section: Clears hypervisor pages. Inclusive start address = 0x%x, exclusive end address = 0x%x; Hypervisor start address = 0x%x.\n", start_va, end_va, HAL_VIRT_START);
		while (1);
	} else if ((start_va & 0x000FFFFF) != 0 || (end_va & 0x000FFFFF) != 0)
		hyper_panic("Address region to clear is not MB aligned\n", 1);

//	printf("HYPERVISOR: linux_clear_virtual_map_section: Clears addresses in [0x%x, 0x%x).\n", start_va & 0xFFF00000, end_va & 0xFFF00000);

	uint32_t va;
	for (va = start_va & 0xFFF00000; va < (end_va & 0xFFF00000); va += SECTION_SIZE) {
//		printf("HV: Removes 0x%x\n", va);
		dmmu_unmap_L1_pageTable_entry(va);
	}

	//Complete memory accesses before invalidating/flushing caches.
	//BPIALL?????????
	dsb();
	isb();
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);	//TLB
	mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback
}

//[@start_pa, @start_pa + size), where @size is number of bytes of memory region
//to map, and spans at most 1MB, and within the same 1MB aligned 1MB memory
//region, implying that the range can be mapped by one page table or one
//section, depending on address alignment.
void linux_boot_second_virtual_map_mb(uint32_t start_va, uint32_t start_pa, uint32_t size, uint32_t page_attrs, uint32_t small_attrs, uint32_t small_attrs_xn) {
	uint32_t guest_pstart = curr_vm->config->firmware->pstart;
	uint32_t guest_vstart = curr_vm->guest_info.page_offset;

	if (size == 0)
		return;
	else if (size > SECTION_SIZE) {
		printf("HYPERVISOR: linux_boot_second_virtual_map_mb: Address range greater than 1MB.\n");
		while (1);
	} else if ((start_va & 0xFFF00000) != ((start_va + size - 1) & 0xFFF00000)) {
		printf("HYPERVISOR: linux_boot_second_virtual_map_mb: Virtual address range spans two different 1MB aligned 1MBs.\n");
		while (1);
	}

	uint32_t table2_pa = pa_to_l2_base_pa(start_pa);
	uint32_t l1_idx = VA_TO_L1_IDX(start_va);			//1MB index of va.
	uint32_t l1_desc = *(flpt_va + l1_idx);				//Virtual address of level-1 descriptor mapping va.
//	printf("HYPERVISOR: linux_boot_second_virtual_map_mb: start_va = %x; start_pa = %x; level-1 descriptor va = %x\n", start_va, start_pa, flpt_va + l1_idx);
	if (L1_TYPE(l1_desc) == UNMAPPED_ENTRY) {	//If va is unmapped, map its level-1 descriptor to its 2nd level page table.
		uint32_t err = dmmu_l1_pt_map(start_va, table2_pa, page_attrs);
		if (err) {
			printf("linux_boot_second_virtual_map_mb0: err = %d\n", err);
			while (1);
		}
	}

	uint32_t table2_index_offset = ((table2_pa - (table2_pa & 0xFFFFF000)) >> 10)*256;
	uint32_t start_table2_index = table2_index_offset + ((start_va & 0x000FF000) >> 12);
	uint32_t end_table2_index = table2_index_offset + (((start_va + size - 1) & 0x000FF000) >> 12);	//Inclusive end index.
	uint32_t page_pa = start_pa & 0xFFFFF000;
	uint32_t i;
	for(i = start_table2_index; i <= end_table2_index; i++, page_pa += 0x1000)
		if (page_pa <= guest_pstart + (curr_vm->config->initial_kernel_ex_va_top - guest_vstart)) {	//Executable code.
			uint32_t err = dmmu_l2_map_entry(table2_pa, i, page_pa, small_attrs);
			if (err == ERR_MMU_PT_NOT_UNMAPPED) {
				/*So DMMU API does not allow changing attributes or remapping an entry if its not empty
				 *this is a workaround */
//printf("HYPERVISOR REMAPS l2pt_linux_entry_va = %x, l2pt_hw_entry_pa = %x, entry_idx = %x, physical level-2 page table base address %x\n", l2pt_linux_entry_va, l2pt_hw_entry_pa & L2_BASE_MASK, entry_idx, MMU_L1_PT_ADDR(phys_pte));
				err = dmmu_l2_unmap_entry(table2_pa, i);
				if (err) {
					printf("linux_boot_second_virtual_map_mb1: err = %d\n", err);
					while (1);
				}
				err = dmmu_l2_map_entry(table2_pa, i, page_pa, small_attrs);
				if (err) {
					printf("linux_boot_second_virtual_map_mb2: err = %d\n", err);
					while (1);
				}
			}
			else if (err) {
				printf("linux_boot_second_virtual_map_mb3: err = %d\n", err);
				while (1);
			}
		} else {																				//Not executable code.
			uint32_t err = dmmu_l2_map_entry(table2_pa, i, page_pa, small_attrs_xn);
			if (err) {
				printf("linux_boot_second_virtual_map_mb4: err = %d\n", err);
				while (1);
			}
		}
	dsb();
	isb();
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);	//TLB
	mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback
}

//Given start_pa and end_pa (exclusive), sets up page tables from start_va to
//start_pa, with 1MB section granularity, covering up to but not including
//end_pa, flushing/invalidation cache/tlb.
void linux_boot_second_virtual_map(uint32_t start_va, uint32_t start_pa, uint32_t end_pa) {
	uint32_t guest_pstart = curr_vm->config->firmware->pstart;
	uint32_t guest_vstart = curr_vm->guest_info.page_offset;
	uint32_t psize = curr_vm->config->firmware->psize;
	if ((start_va & 0x00000FFF) != 0 || (start_pa & 0x00000FFF) != 0 || (end_pa & 0x00000FFF) != 0) {
		printf("HYPERVISOR: linux_boot_second_virtual_map: Not 4kB page aligned addresses.");
		while (1);
	} else if (start_pa < guest_pstart) {
		printf("HYPERVISOR: linux_boot_second_virtual_map: Physical start address below physical start address assigned to Linux.");
		while (1);
	} else if (start_pa > end_pa) {
		printf("HYPERVISOR: linux_boot_second_virtual_map: Physical start address above physical end address.");
		while (1);
	} else if (end_pa > guest_pstart + psize) {
		printf("HYPERVISOR: linux_boot_second_virtual_map: Physical end address above physical end address assigned to Linux.");
		while (1);
	} else if (start_va + end_pa - start_pa > HAL_VIRT_START) {
		printf("HYPERVISOR: linux_boot_second_virtual_map: Virtual end address overlapping hypervisor memory.");
		while (1);
	}

	uint32_t page_attrs = MMU_L1_TYPE_PT | (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
	uint32_t small_attrs = MMU_L2_TYPE_SMALL | MMU_FLAG_B | MMU_FLAG_C | (MMU_AP_USER_RW << MMU_L2_SMALL_AP_SHIFT);
	uint32_t small_attrs_xn = small_attrs | 0b1;

	//Size of first part stopping at the top of the 1st MB section depends on
	//whether the end address is in the same 1MB as the start address or not.
	uint32_t end_va = start_va + (end_pa - start_pa);
	//Virtual addresses must be used since it is the virtual addresses that are
	//split up into 1MB sections.
	uint32_t size = ((end_va - 1) & 0xFFF00000) == (start_va & 0xFFF00000) ? end_va - start_va : SECTION_SIZE - (start_va & 0x000FFFFF);
	linux_boot_second_virtual_map_mb(start_va, start_pa, size, page_attrs, small_attrs, small_attrs_xn);

	//Map intermediate complete MBs.
	for (start_va = start_va + size, start_pa = start_pa + size;
		 start_pa < (end_pa & 0xFFF00000); start_va += SECTION_SIZE, start_pa += SECTION_SIZE)
		linux_boot_second_virtual_map_mb(start_va, start_pa, SECTION_SIZE, page_attrs, small_attrs, small_attrs_xn);

	//Map last MB.
	size = end_pa - start_pa; //May be zero.
	linux_boot_second_virtual_map_mb(start_va, start_pa, size, page_attrs, small_attrs, small_attrs_xn);

	//Complete memory accesses before invalidating/flushing caches.
	//BPIALL?????????
	dsb();
	isb();
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);	//TLB
	mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback
}

//Maps 
//-L4_PER: [0xFA000000, 0xFA000000 + 4MB) -> [0x48000000, 0x48000000 + 4MB)
//-L4_WKUP: [0xF9C00000, 0xF9C00000 + 4MB) -> [0x44C00000, 0x44C00000 + 4MB)
//This is okay since the hypervisor spans [0xF0000000, 0xF010_0000),
//__hyper_start__ = 0xF000_0000, __hyper_end__ = 0xF010_0000 (see
//core/build/sth_beaglebone.map).
#define SZ_4M					0x00400000

#define L4_34XX_SIZE			SZ_4M
#define L4_34XX_BASE			0x48000000
#define OMAP2_L4_IO_OFFSET		0xb2000000
#define L4_34XX_PHYS			L4_34XX_BASE
#define L4_34XX_VIRT			(L4_34XX_PHYS + OMAP2_L4_IO_OFFSET)

#define L4_WK_AM33XX_SIZE		SZ_4M
#define L4_WK_AM33XX_BASE		0x44C00000
#define AM33XX_L4_WK_IO_OFFSET	0xb5000000
#define L4_WK_AM33XX_PHYS		L4_WK_AM33XX_BASE
#define L4_WK_AM33XX_VIRT		(L4_WK_AM33XX_PHYS + AM33XX_L4_WK_IO_OFFSET)

#define CPSW_SS_VIRT 0xFA400000
#define CPSW_SS_PHYS 0x4A100000
#define CPSW_SS_SIZE 0x00004000
#define PRU_ICSS_VIRT (CPSW_SS_VIRT + CPSW_SS_SIZE)
#define PRU_ICSS_PHYS 0x4A300000
#define PRU_ICSS_SIZE 0x00027000
#define TPCC_VIRT (PRU_ICSS_VIRT + PRU_ICSS_SIZE)
#define TPCC_PHYS 0x49000000
#define TPCC_SIZE 0x00001000
#define TPTC0_VIRT (TPCC_VIRT + TPCC_SIZE)
#define TPTC0_PHYS 0x49800000
#define TPTC0_SIZE 0x00001000
#define TPTC1_VIRT (TPTC0_VIRT + TPTC0_SIZE)
#define TPTC1_PHYS 0x49900000
#define TPTC1_SIZE 0x00001000
#define TPTC2_VIRT (TPTC1_VIRT + TPTC1_SIZE)
#define TPTC2_PHYS 0x49A00000
#define TPTC2_SIZE 0x00001000
#define MMCHS2_VIRT (TPTC2_VIRT + TPTC2_SIZE)
#define MMCHS2_PHYS 0x47810000
#define MMCHS2_SIZE 0x00001000
#define USBSS_VIRT (MMCHS2_VIRT + MMCHS2_SIZE)
#define USBSS_PHYS 0x47400000
#define USBSS_SIZE 0x00008000
#define L3OCMC0_VIRT (USBSS_VIRT + USBSS_SIZE)
#define L3OCMC0_PHYS 0x40300000
#define L3OCMC0_SIZE 0x00010000
#define EMIF0_VIRT (L3OCMC0_VIRT + L3OCMC0_SIZE)
#define EMIF0_PHYS 0x4C000000
#define EMIF0_SIZE 0x00001000
#define GPMC_VIRT (EMIF0_VIRT + EMIF0_SIZE)
#define GPMC_PHYS 0x50000000
#define GPMC_SIZE 0x00001000
#define SHAM_VIRT (GPMC_VIRT + GPMC_SIZE)
#define SHAM_PHYS 0x53100000
#define SHAM_SIZE 0x00001000
#define AES_VIRT (SHAM_VIRT + SHAM_SIZE)
#define AES_PHYS 0x53500000
#define AES_SIZE 0x00001000
#define SGX530_VIRT (AES_VIRT + AES_SIZE)
#define SGX530_PHYS 0x56000000
#define SGX530_SIZE 0x00010000
void check_io_mapping(uint32_t start_va, uint32_t start_pa, uint32_t end_pa) {
	uint32_t length = end_pa - start_pa;

	if (start_pa == L4_34XX_PHYS && end_pa == L4_34XX_PHYS + L4_34XX_SIZE && start_va == L4_34XX_VIRT) {
//		printf("Hypervisor check_io_mapping has checked L4_PER 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == L4_WK_AM33XX_PHYS && end_pa == L4_WK_AM33XX_PHYS + L4_WK_AM33XX_SIZE && start_va == L4_WK_AM33XX_VIRT) {
//		printf("Hypervisor check_io_mapping has checked L4_WKUP 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == CPSW_SS_PHYS && end_pa == CPSW_SS_PHYS + CPSW_SS_SIZE && start_va == CPSW_SS_VIRT) {
//		printf("Hypervisor check_io_mapping has checked CPSW_SS 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == PRU_ICSS_PHYS && end_pa == PRU_ICSS_PHYS + PRU_ICSS_SIZE && start_va == PRU_ICSS_VIRT) {
//		printf("Hypervisor check_io_mapping has checked PRU_ICSS 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == TPCC_PHYS && end_pa == TPCC_PHYS + TPCC_SIZE && start_va == TPCC_VIRT) {
//		printf("Hypervisor check_io_mapping has checked TPCC 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == TPTC0_PHYS && end_pa == TPTC0_PHYS + TPTC0_SIZE && start_va == TPTC0_VIRT) {
//		printf("Hypervisor check_io_mapping has checked TPTC0 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == TPTC1_PHYS && end_pa == TPTC1_PHYS + TPTC1_SIZE && start_va == TPTC1_VIRT) {
//		printf("Hypervisor check_io_mapping has checked TPTC1 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == TPTC2_PHYS && end_pa == TPTC2_PHYS + TPTC2_SIZE && start_va == TPTC2_VIRT) {
//		printf("Hypervisor check_io_mapping has checked TPTC2 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == MMCHS2_PHYS && end_pa == MMCHS2_PHYS + MMCHS2_SIZE && start_va == MMCHS2_VIRT) {
//		printf("Hypervisor check_io_mapping has checked MMCHS2 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == USBSS_PHYS && end_pa == USBSS_PHYS + USBSS_SIZE && start_va == USBSS_VIRT) {
//		printf("Hypervisor check_io_mapping has checked USBSS 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == L3OCMC0_PHYS && end_pa == L3OCMC0_PHYS + L3OCMC0_SIZE && start_va == L3OCMC0_VIRT) {
//		printf("Hypervisor check_io_mapping has checked L3OCMC0 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == EMIF0_PHYS && end_pa == EMIF0_PHYS + EMIF0_SIZE && start_va == EMIF0_VIRT) {
//		printf("Hypervisor check_io_mapping has checked EMIF0 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == GPMC_PHYS && end_pa == GPMC_PHYS + GPMC_SIZE && start_va == GPMC_VIRT) {
//		printf("Hypervisor check_io_mapping has checked GPMC 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == SHAM_PHYS && end_pa == SHAM_PHYS + SHAM_SIZE && start_va == SHAM_VIRT) {
//		printf("Hypervisor check_io_mapping has checked SHAM 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == AES_PHYS && end_pa == AES_PHYS + AES_SIZE && start_va == AES_VIRT) {
//		printf("Hypervisor check_io_mapping has checked AES 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else if (start_pa == SGX530_PHYS && end_pa == SGX530_PHYS + SGX530_SIZE && start_va == SGX530_VIRT) {
//		printf("Hypervisor check_io_mapping has checked SGX530 0x%x to 0x%x\n", start_va, start_pa);
		return;
	} else {
		printf("HYPERVISOR: Tries to map invalid device region: start_va = 0x%x; start_pa = 0x%x; end_pa = 0x%x.\n", start_va, start_pa, end_pa);
		while (1);
	}
/*
	//Complete memory accesses before invalidating/flushing caches.
	//BPIALL?????????
	dsb();
	isb();
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);
	mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback

	printf("Hypervisor reads memory[%x] = 0x%x\n", 0xFA100000, *((uint32_t *) 0xFA100000));
*/
}

/* Maps [0xC700_0000, 0xC700_0000 + linux_l2_index_p*2^10) to [0x8800_0000, 0x8800_0000 + linux_l2_index_p*2^10).
 * That is, the mapped linear address space of Linux is extended to include
 * read-only permission for Linux (even though probably only used by the
 * hypervisor) of the second-level page tables. This is necessary for the
 * hypervisor to update certain second-level page tables, which occurs for
 * instance when Linux maps DMA memory
 * (arch/arm/mm/dma-mapping.c:atomic_pool_init by an initcall).
 */
#if 0
void map_l2pts(void) {
	uint32_t guest_pstart = curr_vm->config->firmware->pstart;
	uint32_t guest_vstart = curr_vm->guest_info.page_offset;
	uint32_t guest_psize = curr_vm->config->firmware->psize;
	uint32_t guest_memory_offset = guest_vstart - guest_pstart;	//0xC000_0000 - 0x8100_0000 = 0x3F00_0000

	uint32_t start_pa = guest_pstart + guest_psize;				//0x8100_0000 + 0x7000_0000 = 0x8800_0000
	uint32_t start_va = guest_vstart + guest_psize;				//0xC000_0000 + 0x7000_0000 = 0xC700_0000
	printf("HYPERVISOR map_l2pts guest_memory_offset = %x\n", guest_memory_offset);
	printf("HYPERVISOR map_l2pts start_pa = %x\n", start_pa);
	printf("HYPERVISOR map_l2pts start_va = %x\n", start_va);

	//Number of invocations to linux_pt_get_empty_l2 in
	//linux_init.c:linux_init_dmmu multiplied by 2, since every 2 invocations of
	//linux_pt_get_empty_l2 increments linux_l2_index_p by 4.
	uint32_t linux_l2_index_p = (guest_psize / SECTION_SIZE) * 2;
	uint32_t size = linux_l2_index_p * 1024;					//Every pointer corresponds to 1 level-two page table of size 1kB.
	printf("HYPERVISOR map_l2pts linux_l2_index_p = %x\n", linux_l2_index_p);
	printf("HYPERVISOR map_l2pts size = %x\n", size);
	if (size > SECTION_SIZE) {
		printf("Hypervisor map_l2pts: Too many page tables to map. linux_init.c:linux_init_dmmu should only use 1MB for page tables.\n");
		while (1);
	}

	uint32_t l1_idx = VA_TO_L1_IDX(start_va);									//1MB index of va.
	uint32_t l1_desc = *(flpt_va + l1_idx);										//Virtual address of level-1 descriptor mapping va.

	if (L1_TYPE(l1_desc) != UNMAPPED_ENTRY) {
		printf("HYPERVISOR map_l2pts: l1_desc = 0x%x is mapped.\n", l1_desc);
		while (1);
	}

	uint32_t l1_base_add;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_base_add);
	uint32_t l1_desc_pa_add = L1_IDX_TO_PA(l1_base_add, l1_idx);
	uint32_t *l1_desc_va_add = mmu_guest_pa_to_va(l1_desc_pa_add, curr_vm->config);
	l1_desc = *l1_desc_va_add;

	if ((l1_desc & DESC_TYPE_MASK) == 0) {	//Level one entry is not mapped to a second-level page table.
		printf("HYPERVISOR map_l2pts: l1_desc = 0x%x is not mapped to a second-level page table.\n", l1_desc);
		while (1);
	}

	uint32_t l2_base_pa_add = MMU_L1_PT_ADDR(l1_desc);
	printf("HYPERVISOR map_l2pts l1_desc_ttbr = %x, l2_base_pa_add = %x\n", l1_desc, l2_base_pa_add);

/*	uint32_t l2_idx = 0;
	uint32_t l2_desc_pa_add = L2_IDX_TO_PA(l2_base_pa_add, l2_idx);
	uint32_t l2_desc_va_add = mmu_guest_pa_to_va(l2_desc_pa_add, curr_vm->config);
	uint32_t l2_desc = *((uint32_t *) l2_desc_va_add);
	printf("HYPERVISOR map_l2pts: l2_desc_pa_add = 0x%x, l2_desc = 0x%x\n", l2_desc_pa_add, l2_desc);
*/

	uint32_t start_table2_index = VA_TO_L2_IDX(start_va);
	uint32_t end_table2_index = VA_TO_L2_IDX(start_va + size - 1);		//Inclusive end index.
	uint32_t page_pa = start_pa & 0xFFFFF000;
	uint32_t i;
	for(i = start_table2_index; i <= end_table2_index; i++, page_pa += 0x1000) {
		uint32_t ro_attrs = 0xE | (MMU_AP_USER_RO << MMU_L2_SMALL_AP_SHIFT);	//Read-only for unprivileged Linux.
		uint32_t ret = dmmu_l2_map_entry(l2_base_pa_add, i, page_pa, ro_attrs);	//Here, the mapped page is a page table: read-only.
		printf("HYPERVISOR map_l2pts ret = %x, l2_desc[%d] = &0x%x = %x\n", ret, i, l2_base_pa_add + 4*i,
*((uint32_t *) (mmu_guest_pa_to_va(L2_IDX_TO_PA(l2_base_pa_add, i), curr_vm->config))));
	}

	//Complete memory accesses before invalidating/flushing caches.
	//BPIALL?????????
	dsb();
	isb();
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);
	mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback

//dump_L1pt(curr_vm);

	printf("HYPERVISOR ACCESSES *0xC7013900 = %x\n", *((uint32_t *) 0xC7013900));
while (1);
}
#endif

void print_l2_ap(uint32_t phys_pte) {
	uint32_t new_l2_desc = CREATE_L2_DESC(MMU_L1_PT_ADDR(phys_pte), phys_pte & 0xFFF);
	l2_small_t *pg_desc = (l2_small_t *) (&new_l2_desc);
	uint32_t ap = GET_L2_AP(pg_desc);
	printf("Hypervisor print_l2_ap hypercall_dyn_set_pte: 0x%x\n", ap);
}

#define AP0	(1 << 4)
#define AP1	(1 << 5)
#define AP2	(1 << 9)

void print_ap(uint32_t phys_pte) {
	uint32_t ap0 = (phys_pte & AP0) >> 4;
	uint32_t ap1 = (phys_pte & AP1) >> 4;
	uint32_t ap2 = (phys_pte & AP2) >> 7;
	uint32_t aps = ap0 | ap1 | ap2;

	switch (aps) {
	case 0: printf ("APs0: PL1 = No access, PL0 = No access\n"); break;
	case 1: printf ("APs1: PL1 = RW, PL0 = No access\n"); break;
	case 2: printf ("APs2: PL1 = RW, PL0 = R\n"); break;
	case 3: printf ("APs3: PL1 = RW, PL0 = RW\n"); break;
	case 4: printf ("APs4: Reserved invalid code.\n"); while (1);
	case 5: printf ("APs5: PL1 = R, PL0 = No access\n"); break;
	case 6: printf ("APs6: Deprecated PL1 = R, PL0 = R\n"); while (1);
	case 7: printf ("APs7: PL1 = R, PL0 = R\n"); break;
	default: printf ("APs: Invalid code.\n"); while (1);
	}
}

uint32_t adjust_aps(uint32_t phys_pte) {
	uint32_t ap0 = (phys_pte & AP0) >> 4;
	uint32_t ap1 = (phys_pte & AP1) >> 4;
	uint32_t ap2 = (phys_pte & AP2) >> 7;
	uint32_t aps = ap0 | ap1 | ap2;

	switch (aps) {
			//PL1 = --, PL0 = -- -> PL1 = --, PL0 = --.
	case 0: if (phys_pte) {printf("UNSUPPORTED APs0"); while (1);} return phys_pte;
	case 1: return phys_pte | AP1;							//PL1 = RW, PL0 = -- -> PL1 = RW, PL0 = RW.
	case 2: return phys_pte | AP0;							//PL1 = RW, PL0 = R- -> PL1 = RW, PL0 = RW.
	case 3: return phys_pte;								//PL1 = RW, PL0 = RW -> PL1 = RW, PL0 = RW.
	case 5:	return (phys_pte & ~(AP2 | AP1 | AP0)) | AP1;	//PL1 = R-, PL0 = -- -> PL1 = RW, PL0 = R-.
	case 7: return (phys_pte & ~(AP2 | AP1 | AP0)) | AP1;	//PL1 = R-, PL0 = R- -> PL1 = RW, PL0 = R-.
	case 4: printf ("APs4: Reserved invalid code.\n"); while (1);
	case 6: printf ("APs6: Deprecated PL1 = R, PL0 = R\n"); while (1);
	default: printf ("APs: Invalid code.\n"); while (1);
	}
}

/* Simulates pmd[i] = (pmd[i] & mask) | prot, where pmd[i] maps a section,
 * i ∈ {0, 1}, for all L2 page table entries of the L2 page table pointed to by
 * pmd[i]. A requirement is mask = ~prot.
 */
#define PMD_SECT_XN			(1 << 4)
#define PMD_SECT_APX		(1 << 15)
#define PMD_SECT_AP_WRITE	(1 << 10)
#define AP2					(1 << 9)
#define AP1					(1 << 5)
#define AP0					(1 << 4)
void hypercall_dyn_update_pmd_single(uint32_t pmd, uint32_t mask, uint32_t prot) {
	if (mask != ~prot || (mask != ~PMD_SECT_XN && mask != ~(PMD_SECT_APX | PMD_SECT_AP_WRITE))) {
		printf("hypercall_dyn_update_pmd_single0: Mask and prot are not inverted relative each other.\n");
		while (1);
	}

	uint32_t current_l1_pt_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, current_l1_pt_pa);				//Physical base address of current l1-page table.
	uint32_t l1_pt_va = pmd & L1_BASE_MASK;												//16kB alignment of PMD gives base address of L1 table.
	uint32_t l1_pt_pa = LINUX_PA((addr_t) l1_pt_va);									//Physical base address of L1 page table to modify.
	uint32_t switch_back = 0;
	if (l1_pt_pa != current_l1_pt_pa) {													//If l1-page table to modify is not the current one in use.
		COP_WRITE(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
		isb();
		switch_back = 1;
	}

	uint32_t l1d = *((uint32_t *) pmd);													//L1 descriptor to modify.
	if ((l1d & 0x3) != 0x1) {															//L1 descriptor must point to L2 page table.
		printf("hypercall_dyn_update_pmd_single1: L1 descriptor to modify does not point to an L2 page table: l1d = 0x%x.\n", l1d);
		while (1);
	}

	uint32_t l2_pt_pa = MMU_L1_PT_ADDR(l1d);											//Physical address of L2 page table pointed to by the L1 descriptor the modification of which is to be simulated by this function.
	uint32_t l2_page_pt_va = mmu_guest_pa_to_va(l2_pt_pa & L2_BASE_MASK, curr_vm->config);	//This L2 page table is one of the initial L2s reserved by the hypervisor after physical Linux memory.
	uint32_t table2_idx = (l2_pt_pa - (l2_pt_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT; 	//2 or 3.
	table2_idx *= 0x100;																//256 pages per L2PT.

	uint32_t l2i, err;
	for (l2i = table2_idx; l2i < table2_idx + 256; l2i++) {
		uint32_t l2d = *((uint32_t *)(l2_page_pt_va + 4*l2i));

		if ((l2d & 0x2) == 0x2 && prot == PMD_SECT_XN) {								//Must be valid small page type of l2 entry.
			uint32_t page_pa = MMU_L2_SMALL_ADDR(l2d);									//Page mapped to by current l2 entry.
			uint32_t small_attrs = (0x00000FFF & l2d) | 0x1;							//Sets XN.

			err = dmmu_l2_unmap_entry(l2_pt_pa & L2_BASE_MASK, l2i);
			if (err) {
				printf("hypercall_dyn_update_pmd_single2: err = %d\n", err);
				while (1);
			}

			err = dmmu_l2_map_entry(l2_pt_pa & L2_BASE_MASK, l2i, page_pa, small_attrs);
			if (err) {
				printf("hypercall_dyn_update_pmd_single3: err = %d\n", err);
				while (1);
			}

			COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, l2_page_pt_va + 4*l2i);
		} else if ((l2d & 0x2) == 2) {														//prot == PMD_SECT_APX | PMD_SECT_AP_WRITE due to initial check of this function.
			uint32_t page_pa = MMU_L2_SMALL_ADDR(l2d);									//Page mapped to by current l2 entry.
			uint32_t small_attrs = (0x00000FFF & l2d & ~(AP2 | AP1 | AP0)) | AP1;		//Sets read-only.

			err = dmmu_l2_unmap_entry(l2_pt_pa & L2_BASE_MASK, l2i);
			if (err) {
				printf("hypercall_dyn_update_pmd_single4: err = %d\n", err);
				while (1);
			}

			err = dmmu_l2_map_entry(l2_pt_pa & L2_BASE_MASK, l2i, page_pa, small_attrs);
			if (err) {
				printf("hypercall_dyn_update_pmd_single5: err = %d\n", err);
				while (1);
			}

			COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, l2_page_pt_va + 4*l2i);
		}
	}

	if (switch_back) {
		COP_WRITE(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, current_l1_pt_pa);			//Restore the L1 page table.
		isb();
	}

	clean_and_invalidate_cache();
}

static uint32_t n = 0;
void hypercall_map_block(uint32_t ptr, uint32_t size) {
	uint32_t err;
	uint32_t vstart = curr_vm->config->firmware->vstart;	//or use curr_vm->guest_info.page_offset but they are equal.
	uint32_t pstart = curr_vm->config->firmware->pstart;
	uint32_t psize = curr_vm->config->firmware->psize;

	printf("hypercall_map_block: n = %d\n", n);
	if (n == 46) printf("hypercall_map_block: ptr = 0x%x, size = 0x%x\n", ptr, size);
	if (n == 46) printf("hypercall_map_block: vstart = 0x%x\n", vstart);
	if (n == 46) printf("hypercall_map_block: pstart = 0x%x\n", pstart);
	if (n == 46) printf("hypercall_map_block: psize = 0x%x\n", psize);


	if (!(vstart <= ptr && ptr < vstart + psize)) {
		printf("hypercall_map_block0: Mapped block outside virtual kernel memory region: 0x%x\n", ptr);
		while (1);
	} else if (ptr & 0xFFFF000 != 0x0) {
		printf("hypercall_map_block1: Mapped block not starting on 4kB bountary: 0x%x\n", ptr);
		while (1);
	} else if (size != 0x1000) {
		printf("hypercall_map_block: Mapped block not equal to 4kB: 0x%x\n", size);
		while (1);
	}

	uint32_t ptr_va = ptr;
	uint32_t l1i = ptr_va >> 20;


	uint32_t l1_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pa);
	uint32_t l1_va = mmu_guest_pa_to_va(l1_pa, curr_vm->config);
	uint32_t l1e_va = l1_va + l1i*4;
	uint32_t l1e = *((uint32_t *) l1e_va);
	uint32_t ptr_pa = ptr_va - vstart + pstart;
	uint32_t l2_pa = pa_to_l2_base_pa(ptr_pa);
	uint32_t l2i_start = ((l2_pa - (l2_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT)*256; 	//2 or 3, times 256 gives 512 or 768.
	uint32_t l2i = l2i_start + ((ptr_va & 0x000FF000) >> 12);
	if (n == 46) printf("hypercall_map_block: l1_pa = 0x%x, l1i = 0x%x, l1_va = 0x%x, l1e_va = 0x%x, l1e = 0x%x\n", l1_pa, l1i, l1_va, l1e_va, l1e);
	if (n == 46) printf("hypercall_map_block: l2_pa = 0x%x, l2i = 0x%x, ptr_pa = 0x%x\n", l2_pa, l2i, ptr_pa);
	if ((l1e & 0x3) == 0x0) {	//Unmapped l1 entry.
		dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(l2_pa));
		if (bft_entry->type != PAGE_INFO_TYPE_L2PT || bft_entry->refcnt != 0) {
			printf("hypercall_map_block: Not L2 page table or already"
					" referenced when remapping L1 entry: type = 0x%x, refcnt = 0x%x\n", bft_entry->type, bft_entry->refcnt);
			while (1);
		} else {	//Clear block/4kB page containing the page table.
			uint32_t i;
			if (n == 46) printf("hypercall_map_block: Unmaps l2 entries when remapping initial l2 page table.\n");
			for (i = 512; i < 1024; i++) {
				err = dmmu_l2_unmap_entry(l2_pa, i);
				if (err) {
					printf("hypercall_map_block: Could not unmap l2 entry 0x%x in remap: err = 0x%x.\n", i, err);
					while (1);
				}
			}
		}

		uint32_t page_attrs = MMU_L1_TYPE_PT | (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
		if (n == 46) printf("hypercall_map_block10: START.\n");
		err = dmmu_l1_pt_map(ptr_va, l2_pa, page_attrs);
		if (n == 46) printf("hypercall_map_block10: END.\n");
		if (err) {
			printf("hypercall_map_block0: err = %d\n", err);
			while (1);
		}
	} else if ((l1e & 0x3) == 0x1) {	//L1 entry already mapping. Check if L2 entry is mapping.
		uint32_t l2e_pa = l2_pa + l2i*4;
		uint32_t l2e_va = mmu_guest_pa_to_va(l2e_pa, curr_vm->config);
		uint32_t l2e = *((uint32_t *) l2e_va);
		uint32_t l1e_l2_pa = 0xFFFFFC00 & l1e;

		if (l2_pa != l1e_l2_pa) {
			printf("hypercall_map_block: L1 entry maps to l1e & 0xFFFFFC00 = 0x%x but intended initial l2_pa = 0x%x\n", l1e_l2_pa, l2_pa);
			while (1);
		} else if ((l2e & 0x2) == 1) {	//L2 entry is mapping. Return.
			if ((l2e & 0xFFFFF000) != ptr_pa) {
				printf("hypercall_map_block: L2 entry maps to l2e & 0xFFFFFC00 = 0x%x but should map to ptr_pa = 0x%x\n", l2e, ptr_pa);
				while (1);
			}
			if (n == 46) printf("hypercall_map_block: L1 and L2 are mapping already.\n");
			n++;
			return;
		}
		if (n == 46) printf("hypercall_map_block: L1 is mapping but not L2.\n");
	} else {
		printf("hypercall_map_block: Unknown type field of L1 descriptor: l1e = 0x%x\n", l1e);
		while (1);
	}

	uint32_t small_attrs_xn = MMU_L2_TYPE_SMALL | (MMU_FLAG_B | MMU_FLAG_C) | (MMU_AP_USER_RW << MMU_L2_SMALL_AP_SHIFT) | 0x00000001;
	if (n == 46) printf("hypercall_map_block: Map L2 entry: l2i = 0x%x, l2_pa = 0x%x, ptr_pa = 0x%x\n", l2i, l2_pa, ptr_pa);
	err = dmmu_l2_map_entry(l2_pa, l2i, ptr_pa, small_attrs_xn);
	if (err) {
		printf("hypercall_map_block: Could not map L2 entry on remap: err = %d\n", err);
		while (1);
	}

	clean_and_invalidate_cache();

	printf("hypercall_map_block: Remapped l2 entry to map ptr_va = %x\n", ptr_va);
	printf("hypercall_map_block: BEFORE TEST: memory[0x%x] = 0x%x\n", (uint32_t *) ptr_va, *((uint32_t *) ptr_va));
	*((uint32_t *) ptr_va) = 0x01234567;
	printf("hypercall_map_block: AFTER TEST1: memory[0x%x] = 0x%x\n", (uint32_t *) ptr_va, *((uint32_t *) ptr_va));
	n++;

	memset((void *)ptr_va, 0, size);
	printf("hypercall_map_block: AFTER TEST2: memory[0x%x] = 0x%x\n", (uint32_t *) ptr_va, *((uint32_t *) ptr_va));

}

void hypercall_map_block_nw(uint32_t ptr, uint32_t size) {
	uint32_t err;
	uint32_t vstart = curr_vm->config->firmware->vstart;	//or use curr_vm->guest_info.page_offset but they are equal.
	uint32_t pstart = curr_vm->config->firmware->pstart;
	uint32_t psize = curr_vm->config->firmware->psize;

	printf("hypercall_map_block_nw: n = %d\n", n);
	printf("hypercall_map_block_nw: ptr = 0x%x, size = 0x%x\n", ptr, size);
	printf("hypercall_map_block_nw: vstart = 0x%x\n", vstart);
	printf("hypercall_map_block_nw: pstart = 0x%x\n", pstart);
	printf("hypercall_map_block_nw: psize = 0x%x\n", psize);
while (1);

	if (!(vstart <= ptr && ptr < vstart + psize)) {
		printf("hypercall_map_block_nw0: Mapped block outside virtual kernel memory region: 0x%x\n", ptr);
		while (1);
	} else if (ptr & 0xFFFF000 != 0x0) {
		printf("hypercall_map_block_nw1: Mapped block not starting on 4kB bountary: 0x%x\n", ptr);
		while (1);
	} else if (size != 0x1000) {
		printf("hypercall_map_block_nw2: Mapped block not equal to 4kB: 0x%x\n", size);
		while (1);
	}

	uint32_t ptr_va = ptr;

	uint32_t l1_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pa);
	uint32_t l1_va = mmu_guest_pa_to_va(l1_pa, curr_vm->config);
	uint32_t l1i = ptr_va >> 20;
	uint32_t l1e_va = l1_va + l1i*4;
	uint32_t l1e = *((uint32_t *) l1e_va);

	if ((l1e & 0x3) != 0x1) {
		printf("hypercall_map_block_nw3: L1 entry mapping the pointer is not pointing to an L2 page table: l1_va = 0x%x, l1e_va = 0x%x, l1e = 0x%x\n", l1_va, l1e_va, l1e);
		while (1);
	}

	uint32_t l2_pa = l1e & 0xFFFFFC00;
	uint32_t l2_va = mmu_guest_pa_to_va(l2_pa, curr_vm->config);
	uint32_t l2i = (ptr_va & 0x000FF000) >> 12;
	uint32_t *l2e_va = (uint32_t *)(l2_va + l2i*4);
	uint32_t l2e = *l2e_va;

	if ((l2e & 0x2) == 0x2) {	//Entry valid. So remap it with new access permissions not being writable.
		l2i += ((l2_pa - (l2_pa & 0xFFFFF000)) >> 10)*256;
		err = dmmu_l2_unmap_entry(l2_pa & 0xFFFFF000, l2i);
		if (err) {
			printf("hypercall_map_block_nw4: Cannot unmap entry\n");
			while (1);
		}
		err = dmmu_l2_map_entry(l2_pa & 0xFFFFF000, l2i, l2e & 0xFFFFF000, (l2e & ~(MMU_AP_SUP_RW << MMU_L2_SMALL_AP_SHIFT)) & 0x00000FFF);
		if (err) {
			printf("hypercall_map_block_nw5: Cannot remap entry\n");
			while (1);
		}

		clean_and_invalidate_cache();
	}
}

void merge_with_initial_l2_page_table(uint32_t pmd, uint32_t desc) {
	uint32_t err;
	uint32_t pmd0 = ((uint32_t *) pmd)[0];
	uint32_t pmd1 = ((uint32_t *) pmd)[1];

	if ((pmd0 & 0x3) == 0x1 && (pmd0 & 0xFFFFFC00) >= 0x88000000) {	//L1 table currently pointing to an initial L2 page table.
		uint32_t l2_pa_old = pmd0 & 0xFFFFFC00;
		uint32_t l2_pa_new = desc & 0xFFFFFC00;
		uint32_t l2_va_old = mmu_guest_pa_to_va(l2_pa_old, curr_vm->config);
		uint32_t l2_va_new = mmu_guest_pa_to_va(l2_pa_new, curr_vm->config);
		if ((l2_va_old & 0x00000C00) != 0x800) {	//L2 page table is not 3rd kB of 4kB page.
			printf("merge_with_initial_l2_page_table: L2 page table is not 3rd kB of 4kB page.\n");
			while (1);
		}

		uint32_t l2i;
		for (l2i = 512; l2i < 768; l2i++) {
			uint32_t l2e_va_old = l2_va_old + l2i*4;
			uint32_t l2e_va_new = l2_va_new + l2i*4;
			uint32_t l2e_old = *((uint32_t *) l2e_va_old);
			uint32_t l2e_new = *((uint32_t *) l2e_va_new);
			if ((l2e_old & 0x2) != 0x0 && (l2e_new & 0x2) == 0x0) {	//Valid l2 entry in initial l2, and invalid entry in new l2: Copy.
				printf("merge_with_initial_l2_page_table3: valid old, invalid new.\n");
				err = dmmu_l2_map_entry(l2_pa_new & 0xFFFFF000, l2i, l2e_old & 0xFFFFF000, l2e_old & 0x00000FFF);

				if (err == ERR_MMU_IS_NOT_L2_PT) {
					err = dmmu_create_L2_pt(l2_pa_new & 0xFFFFF000);
					if (err) {
						printf("merge_with_initial_l2_page_table3: Cannot create L2 table, err = %d.\n", err);
						while (1);
					}
					err = dmmu_l2_map_entry(l2_pa_new & 0xFFFFF000, l2i, l2e_old & 0xFFFFF000, l2e_old & 0x00000FFF);
					if (err) {
						printf("merge_with_initial_l2_page_table3: Cannot map L2 entry, err = %d.\n", err);
						while (1);
					}
				} else if (err) {
					printf("merge_with_initial_l2_page_table3: Could not copy L2 entry in L2 table in 4th kB: err = %d\n", err);
					while (1);
				}
			} else if ((l2e_old & 0x2) == 0x0 && (l2e_new & 0x2) != 0x0) {	//Invalid l2 entry in initial l2, and valid entry in new l2: Copy.
//				printf("merge_with_initial_l2_page_table3: invalid old, valid new.\n");
			} else if ((l2e_old & 0x2) != 0x0 && (l2e_new & 0x2) != 0x0) {	//Valid l2 entry in initial l2, and valid entry in new l2: Copy.
//				printf("merge_with_initial_l2_page_table3: valid old, valid new.\n");
			} else if ((l2e_old & 0x2) == 0x0 && (l2e_new & 0x2) == 0x0) {	//Invalid l2 entry in initial l2, and invalid entry in new l2: Copy.
//				printf("merge_with_initial_l2_page_table3: invalid old, invalid new.\n");
			} else {
				printf("merge_with_initial_l2_page_table3: Cannot happen!\n");
				while (1);
			}
		}
	}

	if ((pmd1 & 0x3) == 0x1 && (pmd1 & 0xFFFFFC00) >= 0x88000000) {	//L1 table currently pointing to an initial L2 page table.
		uint32_t l2_pa_old = pmd1 & 0xFFFFFC00;
		uint32_t l2_pa_new = (desc & 0xFFFFFC00) + 0x400;				//Add 1kB for the directly following page table.
		uint32_t l2_va_old = mmu_guest_pa_to_va(l2_pa_old, curr_vm->config);
		uint32_t l2_va_new = mmu_guest_pa_to_va(l2_pa_new, curr_vm->config);
		if ((l2_va_old & 0x00000C00) != 0xC00) {	//L2 page table is not 4th kB of 4kB page.
			printf("merge_with_initial_l2_page_table4: L2 page table is not 4th kB of 4kB page.\n");
			while (1);
		}

		uint32_t l2i;
		for (l2i = 768; l2i < 1024; l2i++) {
			uint32_t l2e_va_old = l2_va_old + (l2i - 768)*4;
			uint32_t l2e_va_new = l2_va_new + (l2i - 768)*4;
			uint32_t l2e_old = *((uint32_t *) l2e_va_old);
			uint32_t l2e_new = *((uint32_t *) l2e_va_new);
			if ((l2e_old & 0x2) != 0x0 && (l2e_new & 0x2) == 0x0) {	//Valid l2 entry in initial l2, and invalid entry in new l2: Copy.
				printf("merge_with_initial_l2_page_table4: valid old, invalid new.\n");
				err = dmmu_l2_map_entry(l2_pa_new & 0xFFFFF000, l2i, l2e_old & 0xFFFFF000, l2e_old & 0x00000FFF);

				if (err == ERR_MMU_IS_NOT_L2_PT) {
					err = dmmu_create_L2_pt(l2_pa_new & 0xFFFFF000);
					if (err) {
						printf("merge_with_initial_l2_page_table4: Cannot create L2 table, err = %d.\n", err);
						while (1);
					}
					err = dmmu_l2_map_entry(l2_pa_new & 0xFFFFF000, l2i, l2e_old & 0xFFFFF000, l2e_old & 0x00000FFF);
					if (err) {
						printf("merge_with_initial_l2_page_table4: Cannot map L2 entry, err = %d.\n", err);
						while (1);
					}
				} else if (err) {
					printf("merge_with_initial_l2_page_table4: Could not copy L2 entry in L2 table in 4th kB: err = %d\n", err);
					while (1);
				}
			} else if ((l2e_old & 0x2) == 0x0 && (l2e_new & 0x2) != 0x0) {	//Invalid l2 entry in initial l2, and valid entry in new l2: Copy.
//				printf("merge_with_initial_l2_page_table4: invalid old, valid new.\n");
			} else if ((l2e_old & 0x2) != 0x0 && (l2e_new & 0x2) != 0x0) {	//Valid l2 entry in initial l2, and valid entry in new l2: Copy.
//				printf("merge_with_initial_l2_page_table4: valid old, valid new.\n");
			} else if ((l2e_old & 0x2) == 0x0 && (l2e_new & 0x2) == 0x0) {	//Invalid l2 entry in initial l2, and invalid entry in new l2: Copy.
//				printf("merge_with_initial_l2_page_table4: invalid old, invalid new.\n");
			} else {
				printf("merge_with_initial_l2_page_table4: Cannot happen!\n");
				while (1);
			}
		}
	}

	clean_and_invalidate_cache();
}

void map_allocated_page_table(uint32_t pte_va) {
	uint32_t ptr_va = pte_va & 0xFFFFF000;

	uint32_t l1_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pa);
	uint32_t l1_va = mmu_guest_pa_to_va(l1_pa, curr_vm->config);
	uint32_t l1i = ptr_va >> 20;
	uint32_t l1e_va = l1_va + l1i*4;
	uint32_t l1e = *((uint32_t *) l1e_va);
	if ((l1e & 0x3) != 0x1) {	//Not valid L1 descriptor
		uint32_t vstart = curr_vm->config->firmware->vstart;	//or use curr_vm->guest_info.page_offset but they are equal.
		uint32_t pstart = curr_vm->config->firmware->pstart;
		uint32_t psize = curr_vm->config->firmware->psize;
		if (ptr_va < vstart || ptr_va >= vstart + psize) {
			printf("map_allocated_page_table: Not valid page table entry address: 0x%x.\n", ptr_va);
			while (1);
		}

		uint32_t ptr_pa = ptr_va - vstart + pstart;
		uint32_t l2_pa = pa_to_l2_base_pa(ptr_pa);	//Physical address of l2 page table mapping pte_va.

		dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(l2_pa));
		if (bft_entry->type != PAGE_INFO_TYPE_L2PT) {
			printf("map_allocated_page_table: L2 page table not marked as such.\n");
			while (1);
		} else {
			printf("map_allocated_page_table: L2 page table marked as such.\n");
			while (1);
		}

		uint32_t l2_va = mmu_guest_pa_to_va(l2_pa, curr_vm->config);
		
	} else if ((l1e & 0x3) == 0x1) {	//Valid L1 descriptor.
		uint32_t l2_pa = l1e & 0xFFFFFC00;
		uint32_t l2_va = mmu_guest_pa_to_va(l2_pa, curr_vm->config);
		uint32_t l2i = (ptr_va & 0x000FF000) >> 12;
		uint32_t *l2e_va = (uint32_t *)(l2_va + l2i*4);
		uint32_t l2e = *l2e_va;
		//USE DMMU HERE!
	} else if ((l1e & 0x3) != 0x0) {
		printf("map_allocated_page_table: Not valid L1 entry.\n");
		while (1);
	}
}

/*
void map_one_to_one_l2(uint32_t start_va, uint32_t end_va, uint32_t prot_l1) {
	uint32_t l1_pa;
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pa);
	uint32_t l1_va = mmu_guest_pa_to_va(l1_pa, curr_vm->config);
	uint32_t l1i = va >> 20;
	uint32_t l1e_va = l1_va + l1i*4;
	uint32_t l1e = *((uint32_t *) l1e_va);
	uint32_t pa = va - vstart + pstart;			//The corresponding physical address of virtual address @va in kernel 1-1 mapping.
	uint32_t l2_pa = pa_to_l2_base_pa(pa);		//Physical address of l2 page table mapping @va to pa.
	if ((l1e & 0x3) != 0x1) {					//Invalid L1 descriptor.

	} else {									//Valid L1 descriptor.
		uint32_t l2_pa = l1e & 0xFFFFFC00;
		uint32_t l2_va = mmu_guest_pa_to_va(l2_pa, curr_vm->config);
		uint32_t l2i = (ptr_va & 0x000FF000) >> 12;
		uint32_t *l2e_va = (uint32_t *)(l2_va + l2i*4);
		uint32_t l2e = *l2e_va;
		l2i += ((l2_pa - (l2_pa & 0xFFFFF000)) >> 10)*256;
		if ((l2e & 0x3) == 0x1) {	//Valid entry.
			err = dmmu_l2_unmap_entry(l2_pa & 0xFFFFF000, l2i);
			if (err) {
				printf("map_one_to_one_l2: Could not unmap entry: l2_pa = 0x%x, l2i = 0x%x", l2_pa, l2i);
				while (1);
			}
			uint32_t attrs = ;
			err = dmmu_l2_map_entry(l2_pa & 0xFFFFF000, l2i, pa & 0xFFFFF000, attrs);
		} else {					//Invalid l2 entry.
		}
	}
}
*/

//https://cpulator.01xz.net/?sys=arm&loadasm=share/s33LHiT.s
//
/*
	bic	r3, r1, #0x000003f0			//r3 := r1 AND ~0x000003f0
	bic	r3, r3, #PTE_TYPE_MASK		//r3 := r3 AND ~PTE_TYPE_MASK = r3 AND ~0x3
	orr	r3, r3, r2					//r3 := r3 OR r2
	orr	r3, r3, #PTE_EXT_AP0 | 2	//r3 := r3 OR (0x10 | 0x2)

	tst	r1, #1 << 4
	orrne	r3, r3, #PTE_EXT_TEX(1)	//If bit 4 is set in r1 (non-zero result, Z flag not set, not equal), then r3 := r3 OR (1 << 6)

	eor	r1, r1, #L_PTE_DIRTY		//r1 := r1 XOR (1 << 6)
	tst	r1, #L_PTE_RDONLY | L_PTE_DIRTY
	orrne	r3, r3, #PTE_EXT_APX	//If either of bits 7 (1 << 7) or 6 (1 << 6) is set in r1, then r3 := r3 OR (1 << 9)

	tst	r1, #L_PTE_USER
	orrne	r3, r3, #PTE_EXT_AP1	//If bit 8 (1 << 8) is set in r1, then r3 := r3 OR (2 << 4)

	tst	r1, #L_PTE_XN
	orrne	r3, r3, #PTE_EXT_XN		//If bit 9 (1 << 9) is set in r1, then r3 := r3 OR (1 << 0)

	tst	r1, #L_PTE_YOUNG
	tstne	r1, #L_PTE_VALID
	eorne	r1, r1, #L_PTE_NONE		//If bit 1 (1 << 1) is set in r1, and if bit 0 (1 << 0) is set in r1, then r1 := r1 XOR (1 << 11)
	tstne	r1, #L_PTE_NONE
	moveq	r3, #0					//If bit 1 (1 << 1) is not set in r1, then r3 := 0
									//If bit 1 (1 << 1) is set in r1, and if bit 0 (1 << 0) is NOT set in r1, then r3 := 0
//If bit 1 (1 << 1) is set in r1, and if bit 0 (1 << 0) is set in r1, and if bit 11 (1 << 11) is NOT set in (r1 XOR (1 << 11)), then r3 := 0
*/
#define PTE_TYPE_MASK	0x3
#define PTE_EXT_AP0		0x10
#define PTE_EXT_TEX(x)	(x << 6)
#define PTE_EXT_APX		(1 << 9)
#define PTE_EXT_AP1		(2 << 4)
#define PTE_EXT_XN		(1 << 0)
#define PTE_EXT_NG		(1 << 11)
#define L_PTE_DIRTY		(1 << 6)
#define L_PTE_RDONLY	(1 << 7)
#define L_PTE_USER		(1 << 8)
#define L_PTE_XN		(1 << 9)
#define L_PTE_YOUNG		(1 << 1)
#define L_PTE_VALID		(1 << 0)
#define L_PTE_NONE		(1 << 11)
#define QUAUX(X) #X
#define QU(X) QUAUX(X)
uint32_t get_pte_hw_i(uint32_t pte_linux, uint32_t ext) {	//ext is global bit.
	asm volatile ("mov	r1, %0" :: "r" (pte_linux) : "r1");
	asm volatile ("mov	r2, %0" :: "r" (ext) : "r2");

	asm volatile ("bic	r3, r1, #0x000003f0" ::: "r3");
	asm volatile ("bic	r3, r3, #" QU(PTE_TYPE_MASK) "" ::: "r3");
	asm volatile ("orr	r3, r3, r2" ::: "r3");
	asm volatile ("orr	r3, r3, #" QU(PTE_EXT_AP0) " | 2" ::: "r3");
	asm volatile ("tst	r1, #1 << 4" ::: "cc");
	asm volatile ("orrne	r3, r3, #" QU(PTE_EXT_TEX(1)) "" ::: "r3");
	asm volatile ("eor	r1, r1, #" QU(L_PTE_DIRTY) "" ::: "r1");
	asm volatile ("tst	r1, #" QU(L_PTE_RDONLY) " | " QU(L_PTE_DIRTY) "" ::: "cc");
	asm volatile ("orrne	r3, r3, #" QU(PTE_EXT_APX) "" ::: "r3");
	asm volatile ("tst	r1, #" QU(L_PTE_USER) "" ::: "cc");
	asm volatile ("orrne	r3, r3, #" QU(PTE_EXT_AP1) "" ::: "r3");
	asm volatile ("tst	r1, #" QU(L_PTE_XN) "" ::: "cc");
	asm volatile ("orrne	r3, r3, #" QU(PTE_EXT_XN) "" ::: "r3");
	asm volatile ("tst	r1, #" QU(L_PTE_YOUNG) "" ::: "cc");
	asm volatile ("tstne	r1, #" QU(L_PTE_VALID) "" ::: "cc");
	asm volatile ("eorne	r1, r1, #" QU(L_PTE_NONE) "" ::: "r1");
	asm volatile ("tstne	r1, #" QU(L_PTE_NONE) "" ::: "cc");
	asm volatile ("moveq	r3, #0" ::: "r3");
	uint32_t pte_hw;
	asm volatile ("mov %0, r3" : "=r" (pte_hw) : :);
	return pte_hw;
}

uint32_t get_pte_hw_c(uint32_t pte_linux, uint32_t ext) {		//ext is global bit.
	uint32_t r1 = pte_linux;
	uint32_t r2 = ext;
	uint32_t r3 = r1 & ~0x000003f0;
	r3 = r3 & ~PTE_TYPE_MASK;
	r3 = r3 | r2;
	r3 = r3 | (PTE_EXT_AP0 | 0x2);

	r3 = r1 & (1 << 4) ? r3 | PTE_EXT_TEX(1) : r3;
	r1 = r1 ^ L_PTE_DIRTY;
	r3 = r1 & (L_PTE_RDONLY | L_PTE_DIRTY) ? r3 | PTE_EXT_APX : r3;
	r3 = r1 & L_PTE_USER ? r3 | PTE_EXT_AP1 : r3;
	r3 = r1 & L_PTE_XN ? r3 | PTE_EXT_XN : r3;
	if (r1 & L_PTE_YOUNG) {
		if (r1 & L_PTE_VALID) {
			r1 = r1 ^ L_PTE_NONE;
			r3 = r1 & L_PTE_NONE ? r3 : 0;
		} else {
			r3 = 0;
		}		
	} else {
		r3 = 0;
	}

	uint32_t pte_hw = r3;
	return pte_hw;
}

uint32_t find_l2_pte_va(uint32_t va, uint32_t pfn) {
	uint32_t pa = pfn << 12;
	uint32_t l2_pa = pa_to_l2_base_pa(pa);
	uint32_t l2_va = mmu_guest_pa_to_va(l2_pa, curr_vm->config);
	uint32_t l2i = (va & 0x000FF000) >> 12;
	uint32_t l2e_va = l2_va + 4*l2i;
	return l2e_va;
}

void hypercall_dyn_set_pte_one_to_one(uint32_t va, uint32_t pfn, uint32_t lpte, uint32_t hpte) {
	uint32_t vstart = curr_vm->config->firmware->vstart;	//or use curr_vm->guest_info.page_offset but they are equal.
	uint32_t page_tables_offset = curr_vm->config->pa_initial_l1_offset;

	uint32_t pa = pfn << 12;
	uint32_t l2_pa = pa_to_l2_base_pa(pa);
	uint32_t l2_va = mmu_guest_pa_to_va(l2_pa, curr_vm->config);
	uint32_t l2i = ((va & 0x000FF000) >> 12) + (((l2_pa - (l2_pa & 0xFFFFF000)) >> 10)*256);

	uint32_t hpte_va = l2_va + ((va & 0x000FF000) >> 12)*4;
	uint32_t lpte_va = hpte_va - 0x800;
	uint32_t attrs = hpte & 0x00000FFF;
	uint32_t err;

	if (hpte != 0) {	//Map.
		if (va == vstart + page_tables_offset + 0x0000 ||	//Page tables must be mapped as read only.
			va == vstart + page_tables_offset + 0x1000 ||
			va == vstart + page_tables_offset + 0x2000 ||
			va == vstart + page_tables_offset + 0x3000 ) {
			attrs = attrs & ~(MMU_AP_SUP_RW << MMU_L2_SMALL_AP_SHIFT);
		}

		err = L2_MAP(l2_pa & 0xFFFFF000, l2i, MMU_L1_PT_ADDR(hpte), attrs);
		if (err == ERR_MMU_PT_NOT_UNMAPPED) {
			err = dmmu_l2_unmap_entry(l2_pa & 0xFFFFF000, l2i);
			if (err) {
				printf("hypercall_dyn_set_pte_one_to_one: dmmu_l2_unmap_entry failed. va = 0x%x, page table at 0xC0004000, err = %d\n", va, err);
				while (1);
			}
			err = L2_MAP(l2_pa & 0xFFFFF000, l2i, MMU_L1_PT_ADDR(hpte), attrs);
		} else if (err == ERR_MMU_PH_BLOCK_NOT_WRITABLE) {	//Tries to map an L2 page table as writable.
			attrs &= ~0x10;									//Clear write permission of new descriptor.
			err = L2_MAP(l2_pa & 0xFFFFF000, l2i, MMU_L1_PT_ADDR(hpte), attrs);
			if (err) {
				printf("Could not mark page as an l2 page table in set pte hypercall when pointing to L2 page: err = %d\n", err);
				while (1);
			}
//			else printf("Could mark page as an l2 page table after remap in set pte hypercall.\n");
		} else {
			printf("hypercall_dyn_set_pte_one_to_one failed: va = 0x%x, page table at 0xC0004000, err = %d\n", va, err);
			while (1);
		}

		if (err == ERR_MMU_PH_BLOCK_NOT_WRITABLE) {	//Tries to map an L2 page table as writable.
			attrs &= ~0x10;									//Clear write permission of new descriptor.
			err = L2_MAP(l2_pa & 0xFFFFF000, l2i, MMU_L1_PT_ADDR(hpte), attrs);
			if (err) {
				printf("Could not mark page as an l2 page table in set pte hypercall when pointing to L2 page: err = %d\n", err);
				while (1);
			}
//			else printf("Could mark page as an l2 page table after remap in set pte hypercall.\n");
		} else if (err) {
			printf("hypercall_dyn_set_pte_one_to_one: vstart = 0x%x, page_tables_offset = 0x%x, vstart + 0x4000 = 0x%x, va = 0x%x, err != 0 && va == vstart + 0x4000 = 0x%x\n", vstart, page_tables_offset, vstart + 0x4000, va, err != 0 && va == vstart + 0x4000);
			printf("hypercall_dyn_set_pte_one_to_one cannot map: l2_pa = 0x%x, l2_va = 0x%x, l2i = %x, va = 0x%x, pfn = 0x%x, hpte = 0x%x, err = %d\n", l2_pa, l2_va, l2i, va, pfn, hpte, err);
			while (1);
		}
	} else {			//Unmap.
		err = dmmu_l2_unmap_entry(l2_pa & 0xFFFFF000, l2i);
		if (err) {
			printf("hypercall_dyn_set_pte_one_to_one cannot unmap: l2_pa = 0x%x, l2_va = 0x%x, l2i = %x, va = 0x%x, pfn = 0x%x, hpte = 0x%x, err = %d\n", l2_pa, l2_va, l2i, va, pfn, hpte, err);
			while (1);
		}
	}

	*((uint32_t *)lpte_va) = lpte;

	COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, hpte_va);
	clean_and_invalidate_cache();
}
