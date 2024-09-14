
#include "hyper.h"
#include "dmmu.h"
#include "guest_blob.h"

// DEBUG FLAGS
#define DEBUG_DMMU_MMU_LEVEL 1

extern virtual_machine *curr_vm;
extern uint32_t *flpt_va;

/* ---------------------------------------------------------------- 
 * BFT helper functions
 * ---------------------------------------------------------------- */
dmmu_entry_t *get_bft_entry_by_block_idx(addr_t ph_block)
{
	dmmu_entry_t *bft = (dmmu_entry_t *) DMMU_BFT_BASE_VA;
	return &bft[ph_block];
}

dmmu_entry_t *get_bft_entry(addr_t adr_py)
{
	return get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(adr_py));
}

void mmu_bft_region_set(addr_t start, size_t size, uint32_t refc, uint32_t x_refc, uint32_t typ)
{
	int n;
	dmmu_entry_t *e = get_bft_entry(start);

	for (n = size >> 12; n-- > 0; e++) {
		e->refcnt = refc;
		e->x_refcnt = x_refc;
		e->type = typ;
	}
}

int mmu_bft_region_type_equals(addr_t start, size_t size, uint32_t type)
{
	int n;
	dmmu_entry_t *e = get_bft_entry(start);

	for (n = size >> 12; n-- > 0; e++) {
		if (e->type != type)
			return 0;
	}
	return 1;
}

int mmu_bft_region_refcnt_equals(addr_t start, size_t size, uint32_t cnt)
{
	int n;
	dmmu_entry_t *e = get_bft_entry(start);

	for (n = size >> 12; n-- > 0; e++) {
		if (e->refcnt != cnt)
			return 0;
	}
	return 1;
}

//TODO Check x_refcnt equals

void dmmu_init()
{
	uint32_t i;
	dmmu_entry_t *bft = (dmmu_entry_t *) DMMU_BFT_BASE_VA;
	printf("bft init %x %x %d\n", DMMU_BFT_BASE_VA, DMMU_BFT_BASE_PY, DMMU_BFT_COUNT);
	/* clear all entries in the table */
	for (i = 0; i < DMMU_BFT_COUNT; i++)
		bft[i].all = 0;
}

BOOL guest_pa_range_checker(pa, size)
{
	// TODO: we are not managing the spatial isolation with the TRUSTED MODE
	uint32_t guest_start_pa = curr_vm->config->firmware->pstart;
	/*Added 1MB to range check, Last +1MB after guest physical address is reserved for L1PT */
	uint32_t guest_end_pa = curr_vm->config->firmware->pstart + curr_vm->config->firmware->psize + SECTION_SIZE;
	if (!((pa >= (guest_start_pa)) && (pa + size <= guest_end_pa)))
		return FALSE;
	return TRUE;
}

BOOL guest_inside_always_cached_region(pa, size)
{
#if CHECK_PAGETABLES_CACHEABILITY
	uint32_t guest_pt_start_pa = curr_vm->config->firmware->pstart + curr_vm->config->always_cached_offset;
	uint32_t guest_pt_end_pa = guest_pt_start_pa + curr_vm->config->always_cached_size;
	if (!((pa >= (guest_pt_start_pa)) && (pa + size <= guest_pt_end_pa)))
		return FALSE;

	return TRUE;
#endif
}

BOOL guest_intersect_always_cached_region(pa, size)
{
	uint32_t guest_pt_start_pa = curr_vm->config->firmware->pstart + curr_vm->config->always_cached_offset;
	uint32_t guest_pt_end_pa = guest_pt_start_pa + curr_vm->config->always_cached_size;
	if ((guest_pt_start_pa <= pa) && (guest_pt_end_pa > pa))
		return TRUE;
	if ((guest_pt_start_pa <= pa + size) && (guest_pt_end_pa >= pa + size))
		return TRUE;
	if ((guest_pt_start_pa >= pa) && (guest_pt_end_pa <= pa + size))
		return TRUE;

	return FALSE;
}

/* -------------------------------------------------------------------
 * L1 creation API it checks validity of created L1 by the guest
 -------------------------------------------------------------------*/
uint32_t l1PT_checker(uint32_t l1_desc)
{
	l1_pt_t *pt = (l1_pt_t *) (&l1_desc);
	dmmu_entry_t *bft_entry_pt = get_bft_entry_by_block_idx(PT_PA_TO_PH_BLOCK(pt->addr));

	uint32_t err_flag = SUCCESS_MMU;

//	if ((pt->addr & 0x2) == 2)
	if ((pt->addr & 0x2) != 0x2) 	//page table in 4 kB page must be at 2kB or 3kB.
		err_flag = ERR_MMU_L2_BASE_OUT_OF_RANGE;
	else if (bft_entry_pt->type != PAGE_INFO_TYPE_L2PT)
		err_flag = ERR_MMU_IS_NOT_L2_PT;
	else if (bft_entry_pt->refcnt >= (MAX_REFCNT - 4096))
		err_flag = ERR_MMU_REF_OVERFLOW;
	else if (pt->pxn)
		err_flag = ERR_MMU_AP_UNSUPPORTED;
	else
		return SUCCESS_MMU;
#if DEBUG_DMMU_MMU_LEVEL > 1
	printf("l1PT_checker failed: %x %d\n", l1_desc, err_flag);
#endif
	return err_flag;
}

uint32_t l1Sec_checker(uint32_t l1_desc, addr_t l1_base_pa_add)
{
	uint32_t ap;
	uint32_t err_flag = SUCCESS_MMU;	// to be set when one of the pages in the section is not a data page
	uint32_t sec_idx;

	l1_sec_t *sec = (l1_sec_t *) (&l1_desc);
	ap = GET_L1_AP(sec);

	// Cacheability attribute check
#ifdef CHECK_PAGETABLES_CACHEABILITY
	if (guest_intersect_always_cached_region
	    (START_PA_OF_SECTION(sec), SECTION_SIZE)) {
		if (sec->c != 1)
			return ERR_MMU_NOT_CACHEABLE;
	}
#endif

	if (sec->secIndic == 1)	// l1_desc is a super section descriptor
		err_flag = ERR_MMU_SUPERSECTION;
	// TODO: (ap != 1) condition need to be added to proof of API
	else if ((ap != 1) && (ap != 2) && (ap != 3))
		err_flag = ERR_MMU_AP_UNSUPPORTED;
	// TODO: Check also that the guest can not read into the hypervisor memory
	// TODO: in general we need also to prevent that it can read from the trusted component, thus identifying a more fine grade control
	//             e.g. using domain
	// TODO: e.g. if you can read in user mode and the domain is the guest user domain or kernel domain then the pa must be in the guest memory
	else if (ap == 3) {
		uint32_t max_kernel_ac =
		    (curr_vm->config->guest_modes[HC_GM_KERNEL]->
		     domain_ac | curr_vm->config->guest_modes[HC_GM_TASK]->
		     domain_ac);
		uint32_t page_domain_mask = (0x3 << (2 * sec->dom));
		uint32_t kernel_ac = max_kernel_ac & page_domain_mask;
		if (kernel_ac != 0) {
			if (!guest_pa_range_checker
			    (START_PA_OF_SECTION(sec), SECTION_SIZE))
				err_flag = ERR_MMU_OUT_OF_RANGE_PA;
		}

		for (sec_idx = 0; sec_idx < 256; sec_idx++) {
			uint32_t ph_block_in_sec = PA_TO_PH_BLOCK(START_PA_OF_SECTION(sec)) | (sec_idx);	// Address of a page in the section
			dmmu_entry_t *bft_entry_in_sec =
			    get_bft_entry_by_block_idx(ph_block_in_sec);

			if (bft_entry_in_sec->type != PAGE_INFO_TYPE_DATA) {
				err_flag = ERR_MMU_PH_BLOCK_NOT_WRITABLE;
			}
			// if one of the L1 page table's pages is in the section
			if (((((uint32_t) ph_block_in_sec) << 12) &
			     L1_BASE_MASK) == l1_base_pa_add) {
				err_flag = ERR_MMU_NEW_L1_NOW_WRITABLE;
			}
			if (bft_entry_in_sec->refcnt >= (MAX_REFCNT - 4096)) {
				err_flag = ERR_MMU_REF_OVERFLOW;
			}
		}
	}
	
	if ((ap == 3 || ap == 2) && sec->xn == 0)
	{
		for(sec_idx = 0; sec_idx < 256; sec_idx++)
		{
			uint32_t ph_block_in_sec = PA_TO_PH_BLOCK(START_PA_OF_SECTION(sec)) | (sec_idx); // Address of a page in the section
			dmmu_entry_t *bft_entry_in_sec = get_bft_entry_by_block_idx(ph_block_in_sec);

			if(bft_entry_in_sec->x_refcnt >= (MAX_REFCNT - 4096))
			{
				err_flag = ERR_MMU_X_REF_OVERFLOW;
			}
		}
	}
	
	if (err_flag != SUCCESS_MMU) {
#if DEBUG_DMMU_MMU_LEVEL >1

		printf("l1Sec_checker failed: %x %x %d\n", l1_desc,
		       l1_base_pa_add, err_flag);
#endif
		return err_flag;
	}

	return err_flag;
}

uint32_t l1Desc_validityChecker_dispatcher(uint32_t l1_type, uint32_t l1_desc, addr_t pgd)
{
	if (l1_type == 0)
		return SUCCESS_MMU;
	if (l1_type == 1) {
//		printf("l1Desc_validityChecker_dispatcher1, l1_desc = 0x%x\n", l1_desc);
		return l1PT_checker(l1_desc);
	}
	if (l1_type == 2) {
//		printf("l1Desc_validityChecker_dispatcher2, l1_desc = 0x%x\n", l1_desc);
		return l1Sec_checker(l1_desc, pgd);
	}
	return ERR_MMU_SUPERSECTION;
}

void create_L1_refs_update(addr_t l1_base_pa_add)
{
	int l1_idx, sec_idx;
	for (l1_idx = 0; l1_idx < 4096; l1_idx++) {
		uint32_t l1_desc_pa_add = L1_IDX_TO_PA(l1_base_pa_add, l1_idx);	// base address is 16KB aligned
		uint32_t l1_desc_va_add = mmu_guest_pa_to_va(l1_desc_pa_add, curr_vm->config);
		uint32_t l1_desc = *((uint32_t *) l1_desc_va_add);
		uint32_t l1_type = l1_desc & DESC_TYPE_MASK;
		if (l1_type == 1) {
			l1_pt_t *pt = (l1_pt_t *) (&l1_desc);
			dmmu_entry_t *bft_entry_pt = get_bft_entry_by_block_idx(PT_PA_TO_PH_BLOCK(pt->addr));
			bft_entry_pt->refcnt += 1;
		} else if (l1_type == 2) {
			l1_sec_t *sec = (l1_sec_t *) (&l1_desc);
			uint32_t ap = GET_L1_AP(sec);
			if (ap == 3) {
				for (sec_idx = 0; sec_idx < 256; sec_idx++) {
					uint32_t ph_block = PA_TO_PH_BLOCK(START_PA_OF_SECTION(sec)) | (sec_idx);
					dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);
					bft_entry->refcnt += 1;
				}
			}

			if (sec->xn == 0 && (ap == 3 || ap == 2))
			{
				for(sec_idx = 0; sec_idx < 256; sec_idx++)
				{
					uint32_t ph_block = PA_TO_PH_BLOCK(START_PA_OF_SECTION(sec)) | (sec_idx);
					dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);
					bft_entry->x_refcnt += 1;
#ifdef DEBUG_X_REF_CREATE_L1
					printf("After creating page table, exe ref counter: %d\n", bft_entry->x_refcnt);
#endif
				}
			}
		}
	}
}

#define DEBUG_PG_CONTENT 1
int dmmu_create_L1_pt(addr_t l1_base_pa_add)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s l1_base_pa_add:%x \n", __func__, l1_base_pa_add);
#endif
	uint32_t l1_idx, pt_idx;
	uint32_t l1_desc;
	uint32_t l1_desc_va_add;
	uint32_t l1_desc_pa_add;
	uint32_t l1_type;
	uint32_t ap;
	uint32_t ph_block;
	int i;

	/*Check that the guest does not override the physical addresses outside its range */
	// TODO, where we take the guest assigned physical memory?
	if (!guest_pa_range_checker(l1_base_pa_add, 4 * PAGE_SIZE))
		return ERR_MMU_OUT_OF_RANGE_PA;

#ifdef CHECK_PAGETABLES_CACHEABILITY
	if (!guest_inside_always_cached_region(l1_base_pa_add, 4 * PAGE_SIZE))
		return ERR_MMU_OUT_OF_CACHEABLE_RANGE;
#endif

	/* 16KB aligned ? */
	if (l1_base_pa_add != (l1_base_pa_add & 0xFFFFC000))
		return ERR_MMU_L1_BASE_IS_NOT_16KB_ALIGNED;

	ph_block = PA_TO_PH_BLOCK(l1_base_pa_add);
	if (get_bft_entry_by_block_idx(ph_block)->type == PAGE_INFO_TYPE_L1PT &&
		get_bft_entry_by_block_idx(ph_block + 1)->type == PAGE_INFO_TYPE_L1PT &&
		get_bft_entry_by_block_idx(ph_block + 2)->type == PAGE_INFO_TYPE_L1PT &&
		get_bft_entry_by_block_idx(ph_block + 3)->type == PAGE_INFO_TYPE_L1PT)
		return ERR_MMU_ALREADY_L1_PT;

	/* try to allocate a PT in physical address */
	if (get_bft_entry_by_block_idx(ph_block)->type != PAGE_INFO_TYPE_DATA ||
		get_bft_entry_by_block_idx(ph_block + 1)->type != PAGE_INFO_TYPE_DATA ||
		get_bft_entry_by_block_idx(ph_block + 2)->type != PAGE_INFO_TYPE_DATA ||
		get_bft_entry_by_block_idx(ph_block + 3)->type != PAGE_INFO_TYPE_DATA)
		return ERR_MMU_PT_REGION;

	if (get_bft_entry_by_block_idx(ph_block)->refcnt != 0 ||
	    get_bft_entry_by_block_idx(ph_block + 1)->refcnt != 0 ||
	    get_bft_entry_by_block_idx(ph_block + 2)->refcnt != 0 ||
	    get_bft_entry_by_block_idx(ph_block + 3)->refcnt != 0) {
		printf("Number of ref %d \n", get_bft_entry_by_block_idx(ph_block + 1)->refcnt);
		return ERR_MMU_REFERENCED;
	}
	// copies  the reserved virtual addresses from the master page table
	// each virtual page non-unmapped in the master page table is considered reserved
	//Copies level-1 descriptors from hypervisor page table to linux page table.
	for (l1_idx = 0; l1_idx < 4096; l1_idx++) {
		l1_desc = *(flpt_va + l1_idx);								//Reads level-1 descriptor from hypervisor page table.
		if (L1_TYPE(l1_desc) != UNMAPPED_ENTRY) {					//level-1 descriptor is mapping.
			l1_desc_pa_add = L1_IDX_TO_PA(l1_base_pa_add, l1_idx);	// base address is 16KB aligned	//Get the physical address of the corresponding (same virtual address range) level-1 descriptor from linux.
			l1_desc_va_add = mmu_guest_pa_to_va(l1_desc_pa_add, curr_vm->config);
			*((uint32_t *) l1_desc_va_add) = l1_desc;				//Write level-1 descriptor to linux page table.
		}
	}

	uint32_t sanity_checker = SUCCESS_MMU;
	for (l1_idx = 0; l1_idx < 4096; l1_idx++) {
		l1_desc_pa_add = L1_IDX_TO_PA(l1_base_pa_add, l1_idx);	// base address is 16KB aligned	//Physical address of l1_idx-th level-1 descriptor.
		l1_desc_va_add = mmu_guest_pa_to_va(l1_desc_pa_add, curr_vm->config);					//Virtual address of l1_idx-th level-1 descriptor.
		l1_desc = *((uint32_t *) l1_desc_va_add);												//l1_idx-th level-1 descriptor.
		l1_type = l1_desc & DESC_TYPE_MASK;

#if DEBUG_DMMU_MMU_LEVEL > 2
		if (l1_desc != 0x0)
			printf("pg %x %x \n", l1_idx, l1_desc);
#endif

		uint32_t current_check = l1Desc_validityChecker_dispatcher(l1_type, l1_desc, l1_base_pa_add);

		if (current_check != SUCCESS_MMU && (l1_idx != 0xFFF && 0xF9C > l1_idx && l1_idx > 0xFA4)) {
			printf("dmmu_create_L1_pt: l1_idx = 0x%x.\n", l1_idx);
#if DEBUG_DMMU_MMU_LEVEL > 1
			printf("L1Create: failed to validate the entry %d: %d \n", l1_idx, current_check);
#endif
			if (sanity_checker == SUCCESS_MMU)
				sanity_checker = current_check;
		}
	}
	if (sanity_checker != SUCCESS_MMU)
		return sanity_checker;

	create_L1_refs_update(l1_base_pa_add);
	get_bft_entry_by_block_idx(ph_block)->type = PAGE_INFO_TYPE_L1PT;
	get_bft_entry_by_block_idx(ph_block + 1)->type = PAGE_INFO_TYPE_L1PT;
	get_bft_entry_by_block_idx(ph_block + 2)->type = PAGE_INFO_TYPE_L1PT;
	get_bft_entry_by_block_idx(ph_block + 3)->type = PAGE_INFO_TYPE_L1PT;

	return SUCCESS_MMU;
}

/* -------------------------------------------------------------------
 * Freeing a given L1 page table
 *  ------------------------------------------------------------------- */
int dmmu_unmap_L1_pt(addr_t l1_base_pa_add)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s l1_base_pa_add:%x \n", __func__, l1_base_pa_add);
#endif
	uint32_t l1_idx, pt_idx, sec_idx;
	uint32_t l1_desc;
	uint32_t l1_desc_va_add;
	uint32_t l1_desc_pa_add;
	uint32_t l1_type;
	uint32_t ap;
	uint32_t ph_block;
	addr_t curr_l1_base_pa_add;
	int i;

	/*Check that the guest does not override the physical addresses outside its range */
	// TODO, where we take the guest assigned physical memory?
	if (!guest_pa_range_checker(l1_base_pa_add, 4 * PAGE_SIZE)) {
		printf("dmmu_unmap_L1_pt0: l1_base_pa_add = 0x%x\n", l1_base_pa_add);
		return ERR_MMU_OUT_OF_RANGE_PA;
	}

	/* 16KB aligned ? */
	if (l1_base_pa_add != (l1_base_pa_add & 0xFFFFC000))
		return ERR_MMU_L1_BASE_IS_NOT_16KB_ALIGNED;

	ph_block = PA_TO_PH_BLOCK(l1_base_pa_add);

	if (get_bft_entry_by_block_idx(ph_block)->type != PAGE_INFO_TYPE_L1PT
	    || get_bft_entry_by_block_idx(ph_block + 1)->type !=
	    PAGE_INFO_TYPE_L1PT
	    || get_bft_entry_by_block_idx(ph_block + 2)->type !=
	    PAGE_INFO_TYPE_L1PT
	    || get_bft_entry_by_block_idx(ph_block + 3)->type !=
	    PAGE_INFO_TYPE_L1PT) {
		return ERR_MMU_IS_NOT_L1_PT;
	}
	// You can not free the current L1
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0,
		 (uint32_t) curr_l1_base_pa_add);
	if ((curr_l1_base_pa_add & 0xFFFFC000) == (l1_base_pa_add & 0xFFFFC000))
		return ERR_MMU_FREE_ACTIVE_L1;

	//unmap_L1_pt_ref_update
	for (l1_idx = 0; l1_idx < 4096; l1_idx++) {
		uint32_t l1_desc_pa_add = L1_IDX_TO_PA(l1_base_pa_add, l1_idx);	// base address is 16KB aligned
		uint32_t l1_desc_va_add =
		    mmu_guest_pa_to_va(l1_desc_pa_add, curr_vm->config);
		uint32_t l1_desc = *((uint32_t *) l1_desc_va_add);
		uint32_t l1_type = l1_desc & DESC_TYPE_MASK;
		if (l1_type == 0)
			continue;
		if (l1_type == 1) {
			l1_pt_t *pt = (l1_pt_t *) (&l1_desc);
			dmmu_entry_t *bft_entry_pt =
			    get_bft_entry_by_block_idx(PT_PA_TO_PH_BLOCK
						       (pt->addr));
			bft_entry_pt->refcnt -= 1;
		}
		if (l1_type == 2) {
			l1_sec_t *sec = (l1_sec_t *) (&l1_desc);
			uint32_t ap = GET_L1_AP(sec);
			if (ap == 3) {
				for (sec_idx = 0; sec_idx < 256; sec_idx++) {
					uint32_t ph_block =
					    PA_TO_PH_BLOCK(START_PA_OF_SECTION
							   (sec)) | (sec_idx);
					dmmu_entry_t *bft_entry =
					    get_bft_entry_by_block_idx
					    (ph_block);
					bft_entry->refcnt -= 1;
				}
			}
			if ((ap == 3 || ap ==2) && sec->xn == 0) {
				for (sec_idx = 0; sec_idx < 256; sec_idx++) {
					uint32_t ph_block =
					    PA_TO_PH_BLOCK(START_PA_OF_SECTION
							   (sec)) | (sec_idx);
					dmmu_entry_t *bft_entry =
					    get_bft_entry_by_block_idx
					    (ph_block);
					bft_entry->x_refcnt -= 1;
				}
			}
		}
	}
	//unmap_L1_pt_pgtype_update
	get_bft_entry_by_block_idx(ph_block)->type = PAGE_INFO_TYPE_DATA;
	get_bft_entry_by_block_idx(ph_block + 1)->type = PAGE_INFO_TYPE_DATA;
	get_bft_entry_by_block_idx(ph_block + 2)->type = PAGE_INFO_TYPE_DATA;
	get_bft_entry_by_block_idx(ph_block + 3)->type = PAGE_INFO_TYPE_DATA;

	return 0;
}

/* -------------------------------------------------------------------
 * Mapping a given section base to the specified entry of L1
 *  -------------------------------------------------------------------*/
//Makes va mapped to 1MB section at physical address sec_base_add.
uint32_t dmmu_map_L1_section(addr_t va, addr_t sec_base_add, uint32_t attrs)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s va:%x sec_base:%x attrs:%x \n", __func__, va,
	       sec_base_add, attrs);
#endif
	uint32_t l1_base_add;
	uint32_t l1_idx;
	uint32_t l1_desc;
	uint32_t l1_desc_va_add;
	uint32_t l1_desc_pa_add;
	uint32_t ap;
	int sec_idx;

	/*Check that the guest does not override the virtual addresses used by the hypervisor */
	// user the master page table to discover if the va is reserved
	// WARNING: we can currently reserve only blocks of 1MB and non single blocks
	//Index of 1MB block of virtual address.
	l1_idx = VA_TO_L1_IDX(va);
	//Obtains the descriptor mapping the 1MB block with virtual address va.
	l1_desc = *(flpt_va + l1_idx);
	if (L1_TYPE(l1_desc) != UNMAPPED_ENTRY) {
		return ERR_MMU_RESERVED_VA;
	}

	/*Check that the guest does not override the physical addresses outside its range */
	// TODO, where we take the guest assigned physical memory?
	if (!guest_pa_range_checker(sec_base_add, SECTION_SIZE))
		return ERR_MMU_OUT_OF_RANGE_PA;

	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, (uint32_t) l1_base_add);	//Reads TTBR0.
	l1_idx = VA_TO_L1_IDX(va);							//Index of 1MB block of virtual address.
	//Physical address of l1_idx-th level-1 descriptor.
	l1_desc_pa_add = L1_IDX_TO_PA(l1_base_add, l1_idx);
	//Virtual address of l1_idx-th level-1 descriptor.
	l1_desc_va_add = mmu_guest_pa_to_va(l1_desc_pa_add, (curr_vm->config));
	//Reads the level-1 descriptor mapping va.
	l1_desc = *((uint32_t *) l1_desc_va_add);
	if (L1_TYPE(l1_desc) != UNMAPPED_ENTRY)
		return ERR_MMU_SECTION_NOT_UNMAPPED;

	// Access permission from the give attribute
	//Creates level-1 1MB section descriptor pointing to sec_base_add.
	l1_desc = CREATE_L1_SEC_DESC(sec_base_add, attrs);

	uint32_t sanity_check = l1Sec_checker(l1_desc, l1_base_add);
	if (sanity_check != SUCCESS_MMU) {
#if DEBUG_DMMU_MMU_LEVEL > 1
		printf("--SANITY CHECK FAILED\n");
#endif
		return sanity_check;
	}

	l1_sec_t *l1_sec_desc = (l1_sec_t *) (&l1_desc);
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("--Attempt to create the desc %x\n", l1_desc);
#endif
	ap = GET_L1_AP(l1_sec_desc);

	if (ap == 3) {
		for (sec_idx = 0; (sec_idx < 256); sec_idx++) {
			uint32_t ph_block = PA_TO_PH_BLOCK(START_PA_OF_SECTION(l1_sec_desc)) | (sec_idx);
			dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);
			bft_entry->refcnt += 1;
		}
	}
	if ((ap == 3 || ap == 2) && l1_sec_desc->xn == 0) {
		for (sec_idx = 0; (sec_idx < 256); sec_idx++) {
			uint32_t ph_block = PA_TO_PH_BLOCK(START_PA_OF_SECTION(l1_sec_desc)) | (sec_idx);
			dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);
			bft_entry->x_refcnt += 1;
		}
	}
	// Update the descriptor in the page table
	//Writes level-1 1MB section descriptor pointing to sec_base_add that maps va.
	*((uint32_t *) l1_desc_va_add) = l1_desc;
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("--Creating a section on the descriptor at %x using %x %b\n", l1_desc_pa_add, l1_desc_va_add, (*((uint32_t *) l1_desc_va_add)));
	printf("--Enabling access to %x\n", sec_base_add);
#endif

	return 0;
}

/* -------------------------------------------------------------------
 * Mapping a given L2 to the specified entry of L1
 *  -------------------------------------------------------------------*/
//Updates the level-1 page table such that @va is mapped by the level-2 page
//table at physical address @l2_base_pa_add.
int dmmu_l1_pt_map(addr_t va, addr_t l2_base_pa_add, uint32_t attrs)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s va:%x l2_base:%x attrs:%x \n", __func__, va, l2_base_pa_add, attrs);
#endif
	uint32_t l1_base_add;
	uint32_t l1_idx;
	uint32_t l1_desc_pa_add;
	uint32_t l1_desc_va_add;
	uint32_t l1_desc;
	uint32_t page_desc;

	// user the master page table to discover if the va is reserved
	// WARNING: we can currently reserve only blocks of 1MB and non single blocks
	l1_idx = VA_TO_L1_IDX(va);					//1MB index of va.
	l1_desc = *(flpt_va + l1_idx);				//Virtual address of level-1 descriptor mapping va.
	if (L1_TYPE(l1_desc) != UNMAPPED_ENTRY) {
		return ERR_MMU_RESERVED_VA;
		while (1) ;
	}

	if (!guest_pa_range_checker(l2_base_pa_add, PAGE_SIZE))
		return ERR_MMU_OUT_OF_RANGE_PA;

	uint32_t ph_block = PA_TO_PH_BLOCK(l2_base_pa_add);
	dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);

	if (bft_entry->type != PAGE_INFO_TYPE_L2PT) {
		return ERR_MMU_IS_NOT_L2_PT;
		while (1) ;
	}

	//l1_base_add = TTBR0.
	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, (uint32_t) l1_base_add);
	l1_idx = VA_TO_L1_IDX(va);					//1MB index of va.

	//The PA byte address of the level-1 descriptor mapping va.
	l1_desc_pa_add = L1_IDX_TO_PA(l1_base_add, l1_idx);

	//The VA byte address of the level-1 descriptor mapping va.
	l1_desc_va_add = mmu_guest_pa_to_va(l1_desc_pa_add, (curr_vm->config));

	//Reads the level-1 descriptor mapping va.
	l1_desc = *((uint32_t *) l1_desc_va_add);

	if (L1_DESC_PXN(attrs)) {
		return ERR_MMU_XN_BIT_IS_ON;
		while (1) ;
	}
	//checks if the L1 entry is unmapped or not
	if ((l1_desc & DESC_TYPE_MASK) != 0) {
		return ERR_MMU_PT_NOT_UNMAPPED;
		while (1) ;
	}

	if (bft_entry->refcnt == MAX_REFCNT) {
		return ERR_MMU_REF_OVERFLOW;
		while (1) ;
	}
	bft_entry->refcnt += 1;
	// Updating memory with the new descriptor
	//Defines the level-1 descriptor by making it point to the given level-2
	//page.
	l1_desc = CREATE_L1_PT_DESC(l2_base_pa_add, attrs);

	l1_pt_t *pt = (l1_pt_t *) (&l1_desc);
//	if ((pt->addr & 0x2) == 2) {
	if ((pt->addr & 0x2) != 0x2) {	//page table in 4 kB page must be at 2kB or 3kB offset from 4kB page start.
printf("dmmu_l1_pt_map ERR_MMU_L2_BASE_OUT_OF_RANGE: va = 0x%x, pt-addr = 0x%x\n", va, pt->addr << 10);
		return ERR_MMU_L2_BASE_OUT_OF_RANGE;
		while (1) ;
	}

	//Writes the descriptor to memory.
	*((uint32_t *) l1_desc_va_add) = l1_desc;

	return 0;
}

/* -------------------------------------------------------------------
 * Freeing an entry of the given L1 page table
 *  ------------------------------------------------------------------- */
uint32_t dmmu_unmap_L1_pageTable_entry(addr_t va)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s va:%x \n", __func__, va);
#endif
	uint32_t l1_base_add;
	uint32_t l1_idx;
	uint32_t l1_desc_pa_add;
	uint32_t l1_desc_va_add;
	uint32_t l1_desc;
	uint32_t l1_type;

	/*Check that the guest does not override the virtual addresses used by the hypervisor */
	// HAL_VIRT_START is usually 0xf0000000, where the hypervisor code/data structures reside
	// user the master page table to discover if the va is reserved
	// WARNING: we can currently reserve only blocks of 1MB and non single blocks
	l1_idx = VA_TO_L1_IDX(va);
	l1_desc = *(flpt_va + l1_idx);
	if (L1_TYPE(l1_desc) != UNMAPPED_ENTRY) {
		return ERR_MMU_RESERVED_VA;
	}

	COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, (uint32_t) l1_base_add);
	l1_idx = VA_TO_L1_IDX(va);
	l1_desc_pa_add = L1_IDX_TO_PA(l1_base_add, l1_idx);
	l1_desc_va_add = mmu_guest_pa_to_va(l1_desc_pa_add, curr_vm->config);	//PA_PT_ADD_VA(l1_desc_pa_add);
	l1_desc = *((uint32_t *) l1_desc_va_add);

#if DEBUG_DMMU_MMU_LEVEL > 3
	printf("--Umpapping %x using %x as %b\n", l1_desc_pa_add, l1_desc_va_add, l1_desc);
#endif
	l1_type = L1_TYPE(l1_desc);
	// We are unmapping a PT
	if (l1_type == 1) {
		l1_pt_t *l1_pt_desc = (l1_pt_t *) (&l1_desc);
		uint32_t ph_block = PA_TO_PH_BLOCK(PA_OF_POINTED_PT(l1_pt_desc));
		dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);
		bft_entry->refcnt -= 1;
		*((uint32_t *) l1_desc_va_add) = UNMAP_L1_ENTRY(l1_desc);
	}
	// We are unmapping a section
	else if ((l1_type == 2) && (((l1_sec_t *) (&l1_desc))->secIndic == 0)) {
		l1_sec_t *l1_sec_desc = (l1_sec_t *) (&l1_desc);
		uint32_t ap = GET_L1_AP(l1_sec_desc);
		int sec_idx;
		if (ap == 3)
			for (sec_idx = 0; sec_idx < 256; sec_idx++) {
				uint32_t ph_block = PA_TO_PH_BLOCK(START_PA_OF_SECTION(l1_sec_desc)) | (sec_idx);
				dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);
				bft_entry->refcnt -= 1;
			}
		if ((ap == 3 || ap ==2) && l1_sec_desc->xn == 0)
			for (sec_idx = 0; sec_idx < 256; sec_idx++) {
				uint32_t ph_block = PA_TO_PH_BLOCK(START_PA_OF_SECTION (l1_sec_desc)) | (sec_idx);
				dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);
				bft_entry->x_refcnt -= 1;
			}
		*((uint32_t *) l1_desc_va_add) = UNMAP_L1_ENTRY(l1_desc);
	}
	// nothing, since the entry was already unmapped
	else {
		return ERR_MMU_ENTRY_UNMAPPED;
	}

	return 0;
}

/* -------------------------------------------------------------------
 * L2 creation API it checks validity of created L2 by the guest
 -------------------------------------------------------------------*/
uint32_t l2PT_checker(addr_t l2_base_pa_add, l2_small_t * pg_desc)
{
	uint32_t ap = ((uint32_t) (pg_desc->ap_3b) << 2) | (pg_desc->ap_0_1bs);
	
	dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(PA_TO_PH_BLOCK (START_PA_OF_SPT(pg_desc)));
#ifdef CHECK_PAGETABLES_CACHEABILITY
	if (guest_intersect_always_cached_region(START_PA_OF_SPT(pg_desc), PAGE_SIZE)) {
		if (pg_desc->c != 1)
			return ERR_MMU_NOT_CACHEABLE;
	}
#endif

	if ((ap != 1) && (ap != 2) && (ap != 3)) {
//		printf("l2PT_checker ERR_MMU_AP_UNSUPPORTED: pg_desc = 0x%x, ap = 0x%x\n", *pg_desc, ap);
		return ERR_MMU_AP_UNSUPPORTED;
	}
	

	if (ap == 3) {
		if (pg_desc->addr == (l2_base_pa_add >> 12))
			return ERR_MMU_NEW_L2_NOW_WRITABLE;
		if (bft_entry->type != PAGE_INFO_TYPE_DATA) {
//			printf("l2PT_checker: ERR_MMU_PH_BLOCK_NOT_WRITABLE. l2 page table at pa = 0x%x, new descriptor = 0x%x, type = 0x%x.\n", l2_base_pa_add, *pg_desc, bft_entry->type);
			return ERR_MMU_PH_BLOCK_NOT_WRITABLE;
		}
		// TODO: Check also that the guest can not read into the hypervisor memory
		// TODO: in general we need also to prevent that it can read from the trusted component, thus identifying a more fine grade control
		//           e.g. using domain
		// TODO: e.g. if you can read in user mode and the domain is the guest user domain or kernel domain then the pa must be in the guest memory
		if (!guest_pa_range_checker (START_PA_OF_SPT(pg_desc), PAGE_SIZE))
			return ERR_MMU_OUT_OF_RANGE_PA;
		if (bft_entry->refcnt >= (MAX_REFCNT - 512)) {
			printf("Overflow (rc=%d) in creating an L2 for the bloxk at the address %x\n", bft_entry->refcnt, START_PA_OF_SPT(pg_desc));
			return ERR_MMU_REF_OVERFLOW;
		}
	}
	if ((ap == 3 || ap == 2) && pg_desc->xn == 0)
	{
		if (bft_entry->x_refcnt >= (MAX_REFCNT - 512))
			return ERR_MMU_X_REF_OVERFLOW;
	}
	return SUCCESS_MMU;
}

uint32_t l2Desc_validityChecker_dispatcher(uint32_t l2_type, uint32_t l2_desc, addr_t l2_base_pa_add)
{
	if (l2_type == 0)
		return SUCCESS_MMU;
	if ((l2_type == 2) || (l2_type == 3))
	{	
		l2_small_t *pg_desc = (l2_small_t *) (&l2_desc);
		return l2PT_checker(l2_base_pa_add, pg_desc);
	}
	return ERR_MMU_L2_UNSUPPORTED_DESC_TYPE;
}


//#define DEBUG_ADDRESS(add) ((add & 0xffff0000) == (0x86610000 & 0xffff0000))

void create_L2_refs_update(addr_t l2_base_pa_add)
{
	uint32_t l2_desc_pa_add;
	uint32_t l2_desc_va_add;
	int l2_idx;
//	for (l2_idx = 0; l2_idx < 512; l2_idx++) {
	for (l2_idx = 512; l2_idx < 1024; l2_idx++) {
		l2_desc_pa_add = L2_DESC_PA(l2_base_pa_add, l2_idx);	// base address is 4KB aligned
		l2_desc_va_add = mmu_guest_pa_to_va(l2_desc_pa_add, curr_vm->config);
		uint32_t l2_desc = *((uint32_t *) l2_desc_va_add);
		uint32_t l2_type = l2_desc & DESC_TYPE_MASK;
		l2_small_t *pg_desc = (l2_small_t *) (&l2_desc);
		if ((l2_type == 2) || (l2_type == 3)) {
			uint32_t ap = GET_L2_AP(pg_desc);
			uint32_t ph_block = PA_TO_PH_BLOCK(START_PA_OF_SPT(pg_desc));
			dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);

#ifdef DEBUG_ADDRESS
			if (DEBUG_ADDRESS(START_PA_OF_SPT(pg_desc)))
				printf("[DMMU] I am called %s mapping pa:%x using pt at:%x idx:%d attr:%x rc=%d\n", __func__, START_PA_OF_SPT(pg_desc), l2_base_pa_add, l2_idx, ap, bft_entry->refcnt);
#endif

			if ((bft_entry->type == PAGE_INFO_TYPE_DATA) && (ap == 3))
				bft_entry->refcnt += 1;
			if ((bft_entry->type == PAGE_INFO_TYPE_DATA) && ((ap == 3 || ap == 2) && pg_desc->xn == 0))
				bft_entry->x_refcnt += 1;
#ifdef DEBUG_ADDRESS
			if (DEBUG_ADDRESS(START_PA_OF_SPT(pg_desc)))
				printf("[DMMU] new rc=%d\n",bft_entry->refcnt);
#endif

		}
	}
}

void create_L2_pgtype_update(uint32_t l2_base_pa_add)
{
	uint32_t ph_block = PA_TO_PH_BLOCK(l2_base_pa_add);
	dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);
	bft_entry->type = PAGE_INFO_TYPE_L2PT;
}

//@l2_base_pa_add: Start physical address of memory containing level-2 page
//table.
//
//Updates DMMU to reflect a new level-2 page table by reading 512 level-2
//descriptors stored in 2kB memory.
uint32_t dmmu_create_L2_pt(addr_t l2_base_pa_add)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s  l2_base:%x \n", __func__, l2_base_pa_add);
#endif
	uint32_t l2_desc_pa_add;
	uint32_t l2_desc_va_add;
	uint32_t l2_desc;
	uint32_t l2_type;
	uint32_t l2_idx;
	//Virtual physical address of memory containing level-2 page table.
	uint32_t l2_base_va_add = mmu_guest_pa_to_va(l2_base_pa_add, curr_vm->config);

	/*Check that the guest does not override the physical addresses outside its range */
	// TODO, where we take the guest assigned physical memory?
	//
	if (!guest_pa_range_checker(l2_base_pa_add, PAGE_SIZE))	//PAGE_SIZE = 0x0000_1000
		return ERR_MMU_OUT_OF_RANGE_PA;

#ifdef CHECK_PAGETABLES_CACHEABILITY
	if (!guest_inside_always_cached_region(l2_base_pa_add, PAGE_SIZE))
		return ERR_MMU_OUT_OF_CACHEABLE_RANGE;
#endif

	//not 4KB aligned ?
	//L2_BASE_MASK = 0xFFFFF000
	//4kB aligned allows ORing address with descriptor configuration bits (lower
	//12 bits) to form the descriptor.
	if (l2_base_pa_add != (l2_base_pa_add & L2_BASE_MASK))
		return ERR_MMU_BASE_ADDRESS_IS_NOT_ALIGNED;

	uint32_t ph_block = PA_TO_PH_BLOCK(l2_base_pa_add);
	dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);

	if (bft_entry->type == PAGE_INFO_TYPE_L2PT)
		return ERR_MMU_ALREADY_L2_PT;

	// try to allocate a PT in either a PT page physical address or a referenced data page physical address
	if (bft_entry->type == PAGE_INFO_TYPE_L1PT)
		return ERR_MMU_PT_REGION;
	if ((bft_entry->type == PAGE_INFO_TYPE_DATA) && (bft_entry->refcnt != 0))
		return ERR_MMU_REFERENCED;

	uint32_t sanity_checker = SUCCESS_MMU;
	//Checks 512 page table entries = 2kB, remaining 2kB is metadata since ARM
	//Linux uses 512 entries per level-2 page table.
//	for (l2_idx = 0; l2_idx < 512; l2_idx++) {
	for (l2_idx = 512; l2_idx < 1024; l2_idx++) {
		//Physical byte address of current level-2 descriptor.
		l2_desc_pa_add = L2_DESC_PA(l2_base_pa_add, l2_idx);	// base address is 4KB aligned
		//Virtual byte address of current level-2 descriptor
		l2_desc_va_add = mmu_guest_pa_to_va(l2_desc_pa_add, curr_vm->config);
		l2_desc = *((uint32_t *) l2_desc_va_add);			//Read descriptor.
		l2_type = l2_desc & DESC_TYPE_MASK;
		uint32_t current_check = l2Desc_validityChecker_dispatcher(l2_type, l2_desc, l2_base_pa_add);

		if (current_check != SUCCESS_MMU) {
#if DEBUG_DMMU_MMU_LEVEL > 1
			printf("Sanity checker error %d!: %d : %x : %x\n", current_check, l2_idx, l2_desc_pa_add, l2_desc);
#endif
			if (sanity_checker == SUCCESS_MMU)
				sanity_checker = current_check;
		}
	}

	if (sanity_checker != SUCCESS_MMU)
		return sanity_checker;

	//Update DMMU data structures.
	create_L2_refs_update(l2_base_pa_add);
	create_L2_pgtype_update(l2_base_pa_add);

	return SUCCESS_MMU;
}

/* -------------------------------------------------------------------
 * Freeing a given L2 page table
 *  -------------------------------------------------------------------*/
int dmmu_unmap_L2_pt(addr_t l2_base_pa_add)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s l2_base_pa_add:%x \n", __func__, l2_base_pa_add);
#endif
	uint32_t l2_desc_pa_add;
	uint32_t l2_desc_va_add;
	uint32_t l2_desc;
	uint32_t l2_type;
	uint32_t ap;		// access permission
	int l2_idx;

	if (!guest_pa_range_checker(l2_base_pa_add, PAGE_SIZE))
		return ERR_MMU_OUT_OF_RANGE_PA;

	uint32_t ph_block = PA_TO_PH_BLOCK(l2_base_pa_add);
	dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);

	// not 4KB aligned ?
	if ((bft_entry->type != PAGE_INFO_TYPE_L2PT) || (l2_base_pa_add != (l2_base_pa_add & L2_BASE_MASK)))
		return ERR_MMU_IS_NOT_L2_PT;

	// There should be no reference to the page in the time of unmapping
	if (bft_entry->refcnt > 0) {
//kanske ta bort referenserna.
//print_all_pointing_L1(l2_base_pa_add, 0xFFFFFFFF);
//print_all_pointing_L2(l2_base_pa_add, 0xFFFFFFFF);
//		printf("dmmu_unmap_L2_pt: Reference to L2 page table being unmapped from L1 entry.\n");	//Could be due to mapping used by hypervisor.
//while (1);
//		return ERR_MMU_REFERENCE_L2;
	}

	//updating the entries of L2
//	for (l2_idx = 0; l2_idx < 512; l2_idx++) {
	for (l2_idx = 512; l2_idx < 1024; l2_idx++) {
		l2_desc_pa_add = L2_DESC_PA(l2_base_pa_add, l2_idx);	// base address is 4KB aligned
		l2_desc_va_add = mmu_guest_pa_to_va(l2_desc_pa_add, curr_vm->config);
		l2_desc = *((uint32_t *) l2_desc_va_add);
		l2_small_t *pg_desc = (l2_small_t *) (&l2_desc);
		dmmu_entry_t *bft_entry_pg = get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(START_PA_OF_SPT(pg_desc)));
		ap = GET_L2_AP(pg_desc);
		l2_type = l2_desc & DESC_TYPE_MASK;

		if (l2_type == 0)
			continue;
		if ((l2_type == 2) || (l2_type == 3)) {
#ifdef DEBUG_ADDRESS
			if (DEBUG_ADDRESS(START_PA_OF_SPT(pg_desc)))
				printf("[DMMU] I am called %s unmapping pa:%x using pt at:%x idx:%d attr:%x rc=%d\n", __func__, START_PA_OF_SPT(pg_desc),
				       l2_base_pa_add, l2_idx, ap, bft_entry_pg->refcnt);
#endif

			if (ap == 3)
				bft_entry_pg->refcnt -= 1;
			if ((ap == 3 || ap == 2) && pg_desc->xn == 0)
				bft_entry_pg->x_refcnt -= 1;

#ifdef DEBUG_ADDRESS
			if (DEBUG_ADDRESS(START_PA_OF_SPT(pg_desc)))
				printf("New rc=%d ex=%d\n", bft_entry_pg->refcnt, bft_entry_pg->x_refcnt);
#endif

		}
	}

	//Changing the type of the L2 page table to data page
	bft_entry->type = PAGE_INFO_TYPE_DATA;

	return 0;
}

/* -------------------------------------------------------------------
 * Mapping a given page to the specified entry of L2
 *  -------------------------------------------------------------------*/
//Maps level-2 entry at @l2_idx-th index of level-2 page table at physical
//address @l2_base_pa_add to physical 4kB page at @page_pa_add.
int dmmu_l2_map_entry(addr_t l2_base_pa_add, uint32_t l2_idx, addr_t page_pa_add, uint32_t attrs)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s mapping pg:%x to:%x \n", __func__, page_pa_add, l2_base_pa_add);
#endif
	uint32_t l2_desc_pa_add;
	uint32_t l2_desc_va_add;
	uint32_t l2_desc;
	uint32_t ap;		// access permission

	/*Check that the guest does not override the physical addresses outside its range */
	if (!guest_pa_range_checker(l2_base_pa_add, PAGE_SIZE)) {
printf("Hypervisor dmmu_l2_map_entry1: l2_base_pa_add = 0x%x\n", l2_base_pa_add);
		return ERR_MMU_OUT_OF_RANGE_PA;
}
	if (!guest_pa_range_checker(page_pa_add, PAGE_SIZE)) {
printf("Hypervisor dmmu_l2_map_entry2: page_pa_add = 0x%x\n", page_pa_add);
		return ERR_MMU_OUT_OF_RANGE_PA;
}

	//Physical address of the l2_idx-th entry of the level-2 page table at
	//physical address l2_base_pa_add (l2_base_add is 4kB aligned and has 1024
	//entries).
	l2_desc_pa_add = L2_IDX_TO_PA(l2_base_pa_add, l2_idx);
	//Virtual address of the l2_idx-th entry of the level-2 page table at
	//virtual address l2_base_va_add (l2_base_add is 4kB aligned and has 1024
	//entries).
	l2_desc_va_add = mmu_guest_pa_to_va(l2_desc_pa_add, curr_vm->config);

	// Finding the corresponding entry for the page_pa_add and l2_base_pa_add in BFT
	uint32_t ph_block_pg = PA_TO_PH_BLOCK(page_pa_add);
	dmmu_entry_t *bft_entry_pg = get_bft_entry_by_block_idx(ph_block_pg);

	uint32_t ph_block_pt = PA_TO_PH_BLOCK(l2_base_pa_add);
	dmmu_entry_t *bft_entry_pt = get_bft_entry_by_block_idx(ph_block_pt);

	if (bft_entry_pt->type != PAGE_INFO_TYPE_L2PT) {
//printf("Hypervisor dmmu_l2_map_entry3: l2_base_pa_add = 0x%x, l2_idx = 0x%x, page_pa_add = 0x%x, bft_entry_pt->type = 0x%x\n", l2_base_pa_add, l2_idx, page_pa_add, bft_entry_pt->type);
		return ERR_MMU_IS_NOT_L2_PT;
}

	l2_desc = *((uint32_t *) l2_desc_va_add);
#ifdef DEBUG_ADDRESS
	if (DEBUG_ADDRESS(page_pa_add))
		printf("[DMMU] I am called %s mapping pa:%x using pt at:%x idx=%d old_desx=0x%x\n", __func__, page_pa_add, l2_base_pa_add, l2_idx, l2_desc);
#endif

	//checks if the L2 entry is unmapped or not
	if ((l2_desc & DESC_TYPE_MASK) != 0) {
//printf("Hypervisor dmmu_l2_map_entry4: l2_desc = 0x%x\n", l2_desc);
		return ERR_MMU_PT_NOT_UNMAPPED;
}

	//Creates a level two descriptor mapping to the physical 4kB page at
	//page_pa_add.
	uint32_t new_l2_desc = CREATE_L2_DESC(page_pa_add, attrs);
	uint32_t sanity_check = l2PT_checker(l2_base_pa_add, &new_l2_desc);
	if (sanity_check != SUCCESS_MMU) {
//printf("Hypervisor dmmu_l2_map_entry5: sanity_check = 0x%x, attrs = 0x%x\n", sanity_check, attrs);
		return sanity_check;
}

	//Updating page reference counter
	l2_small_t *pg_desc = (l2_small_t *) (&new_l2_desc);
	ap = GET_L2_AP(pg_desc);

#ifdef DEBUG_ADDRESS
	if (DEBUG_ADDRESS(START_PA_OF_SPT(pg_desc)))
		printf("[DMMU] I am called %s mapping pa:%x using pt at:%x idx=%d attr:%x ap=%x rc=%d\n", __func__, START_PA_OF_SPT(pg_desc), l2_base_pa_add, l2_idx, attrs, ap, bft_entry_pg->refcnt);
#endif

	if (ap == 3)
		bft_entry_pg->refcnt += 1;
	if ((ap == 3 || ap == 2) && pg_desc->xn == 0)
		bft_entry_pg->x_refcnt += 1;

#ifdef DEBUG_ADDRESS
	if (DEBUG_ADDRESS(START_PA_OF_SPT(pg_desc)))
		printf("New rc=%d ex=%d\n", bft_entry_pg->refcnt, bft_entry_pg->x_refcnt);
#endif
	//Updating page table in memory
	//Stores the level two descriptor mapping to the physical 4kB page at
	//page_pa_add in the l2_idx-th entry of the level-2 page table at
	//virtual address l2_base_va_add.
	*((uint32_t *) l2_desc_va_add) = new_l2_desc;
//printf("Hypervisor dmmu_l2_map_entry6\n");
	return SUCCESS_MMU;
}

/* -------------------------------------------------------------------
 * Unmapping an entry of given L2 page table
 *  -------------------------------------------------------------------*/
//Marks descriptor with index @l2_idx of level-2 page table at @l2_base_pa_add
//as unmapped.
int dmmu_l2_unmap_entry(addr_t l2_base_pa_add, uint32_t l2_idx)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s l2_base_pa_add:%x l2_idx:%x \n", __func__,
	       l2_base_pa_add, l2_idx);
#endif
	uint32_t l2_desc_pa_add;
	uint32_t l2_desc_va_add;
	uint32_t l2_desc;
	uint32_t l2_type;
	uint32_t ap;		// access permission

	if (!guest_pa_range_checker(l2_base_pa_add, PAGE_SIZE))
		return ERR_MMU_OUT_OF_RANGE_PA;

	uint32_t ph_block = PA_TO_PH_BLOCK(l2_base_pa_add);
	dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(ph_block);

	if (bft_entry->type != PAGE_INFO_TYPE_L2PT)
		return ERR_MMU_IS_NOT_L2_PT;

	//Get physical address of level-2 descriptor at index @l2_idx of level-2
	//page at l2_base_pa_add.
	l2_desc_pa_add = L2_IDX_TO_PA(l2_base_pa_add, l2_idx);
	//Virtual address of level-2 descriptor via the address space used by the
	//hypervisor to read Linux memory.
	l2_desc_va_add = mmu_guest_pa_to_va(l2_desc_pa_add, (curr_vm->config));
	//Read level-2 descriptor.
	l2_desc = *((uint32_t *) l2_desc_va_add);
	l2_type = l2_desc & DESC_TYPE_MASK;

	if ((l2_type != 0x2) && (l2_type != 0x3))
		return 0;

	l2_small_t *pg_desc = (l2_small_t *) (&l2_desc);
	dmmu_entry_t *bft_entry_pg = get_bft_entry_by_block_idx(PA_TO_PH_BLOCK (START_PA_OF_SPT(pg_desc)));

	ap = GET_L2_AP(pg_desc);

#ifdef DEBUG_ADDRESS
	if (DEBUG_ADDRESS(START_PA_OF_SPT(pg_desc)))
		printf("[DMMU] I am called %s unmapping pa:%x using pt at:%x ap=%x rc=%d\n", __func__, START_PA_OF_SPT(pg_desc), l2_base_pa_add, ap, bft_entry_pg->refcnt);
#endif


	if (ap == 3)
		bft_entry_pg->refcnt -= 1;

	if ((ap == 3 || ap == 2) && pg_desc->xn == 0)
		bft_entry_pg->x_refcnt -= 1;

#ifdef DEBUG_ADDRESS
	if (DEBUG_ADDRESS(START_PA_OF_SPT(pg_desc)))
		printf("New rc=%d\n", bft_entry_pg->refcnt);
#endif

	//Updating page table in memory
	l2_desc = UNMAP_L2_ENTRY(l2_desc);			//Marks descriptor as invalid/unmapped.
	*((uint32_t *) l2_desc_va_add) = l2_desc;	//Stores descriptor back.

	return 0;
}

/* -------------------------------------------------------------------
 * Switching active L1 page table
 *  -------------------------------------------------------------------*/
//#define SW_DEBUG
int dmmu_switch_mm(addr_t l1_base_pa_add)
{
#if DEBUG_DMMU_MMU_LEVEL > 2
	printf("I am called %s  l1_base:%x \n", __func__, l1_base_pa_add);
#endif

	int i;
	uint32_t ph_block;

	/*Check that the guest does not override the physical addresses outside its range */
	// TODO, where we take the guest assigned physical memory?
	if (!guest_pa_range_checker(l1_base_pa_add, 4 * PAGE_SIZE))
		return ERR_MMU_OUT_OF_RANGE_PA;

	/* 16KB aligned ? */
	if (l1_base_pa_add != (l1_base_pa_add & 0xFFFFC000))
		return ERR_MMU_L1_BASE_IS_NOT_16KB_ALIGNED;

	ph_block = PA_TO_PH_BLOCK(l1_base_pa_add);

	if (get_bft_entry_by_block_idx(ph_block)->type != PAGE_INFO_TYPE_L1PT)
		return ERR_MMU_IS_NOT_L1_PT;
#if DEBUG_DMMU_MMU_LEVEL > 3
	uint32_t l1_idx;
	for (l1_idx = 0; l1_idx < 4096; l1_idx++) {
		uint32_t l1_desc_pa_add = L1_IDX_TO_PA(l1_base_pa_add, l1_idx);	// base address is 16KB aligned
		uint32_t l1_desc_va_add = mmu_guest_pa_to_va(l1_desc_pa_add, curr_vm->config);
		uint32_t l1_desc = *((uint32_t *) l1_desc_va_add);
		if (l1_desc != 0x0)
			printf("pg %x %x \n", l1_idx, l1_desc);
	}
#endif

	// Switch the TTB and set context ID
	COP_WRITE(COP_SYSTEM, COP_CONTEXT_ID_REGISTER, 0);	//Set reserved context ID
	isb();
	/* activate the guest page table */
	COP_WRITE(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_base_pa_add);	// Set TTB0
	return 0;
}

// ----------------------------------------------------------------

enum dmmu_command {
	CMD_MAP_L1_SECTION, CMD_UNMAP_L1_PT_ENTRY, CMD_CREATE_L2_PT,
	CMD_MAP_L1_PT, CMD_MAP_L2_ENTRY, CMD_UNMAP_L2_ENTRY, CMD_FREE_L2,
	CMD_CREATE_L1_PT, CMD_SWITCH_ACTIVE_L1, CMD_FREE_L1
};

int dmmu_handler(uint32_t p03, uint32_t p1, uint32_t p2)
{
	uint32_t p0 = p03 & 0xF;
	uint32_t p3 = p03 >> 4;

#if DEBUG_DMMU_MMU_LEVEL > 1
	printf("dmmu_handler: DMMU %x %x %x\n", p1, p2, p3);
#endif

	switch (p0) {
	case CMD_CREATE_L1_PT:
		return dmmu_create_L1_pt(p1);
	case CMD_FREE_L1:
		return dmmu_unmap_L1_pt(p1);
	case CMD_MAP_L1_SECTION:
		return dmmu_map_L1_section(p1, p2, p3);
	case CMD_MAP_L1_PT:
		return dmmu_l1_pt_map(p1, p2, p3);
	case CMD_UNMAP_L1_PT_ENTRY:
		return dmmu_unmap_L1_pageTable_entry(p1);
	case CMD_CREATE_L2_PT:
		return dmmu_create_L2_pt(p1);
	case CMD_FREE_L2:
		return dmmu_unmap_L2_pt(p1);
	case CMD_MAP_L2_ENTRY:
		p3 = p03 & 0xFFFFFFF0;
		uint32_t idx = p2 >> 20;
		uint32_t attrs = p2 & 0xFFF;
		return dmmu_l2_map_entry(p1, idx, p3, attrs);
	case CMD_UNMAP_L2_ENTRY:
		return dmmu_l2_unmap_entry(p1, p2);
	case CMD_SWITCH_ACTIVE_L1:
		return dmmu_switch_mm(p1);
	default:
		return ERR_MMU_UNIMPLEMENTED;
	}
}

uint32_t dmmu_query_bft(uint32_t pa) {
	uint32_t ph_block;

	ph_block = PA_TO_PH_BLOCK(pa);
	return get_bft_entry_by_block_idx(ph_block)->all;
}

void print_all_pointing_L1(uint32_t pa, uint32_t mask)
{
	uint32_t ph_block_pg = PA_TO_PH_BLOCK(pa);
	dmmu_entry_t *bft_entry_pg = get_bft_entry_by_block_idx(ph_block_pg);

	uint32_t i = 0;
	uint32_t l1_idx;
	uint32_t number_of_l1 = 0;

	for (i = 0; i < (1 << 20); i += 4) {
		uint32_t sec_mask = 0xfff00000 & mask;
		dmmu_entry_t *bft_entry = get_bft_entry_by_block_idx(i);

		if (bft_entry->type != PAGE_INFO_TYPE_L1PT)
			continue;

		printf("   checking block %d\n", i);

		for (l1_idx = 0; l1_idx < 4096; l1_idx += 1) {
			uint32_t l1_desc_pa_add = L1_IDX_TO_PA(START_PA_OF_BLOCK(i), l1_idx);
			uint32_t l1_desc_va_add = mmu_guest_pa_to_va(l1_desc_pa_add, curr_vm->config);
			uint32_t l1_desc = *((uint32_t *) l1_desc_va_add);
			uint32_t l1_type = L1_TYPE(l1_desc);
 			if (l1_type == 1 && (l1_desc & 0xFFFFFC00) == pa) {
				printf("   The L1 page table entry in 0x%x (index %x) points to 0x%x\n", START_PA_OF_BLOCK(i), l1_idx, pa);
				printf("      va is %x, desc = 0x%x\n", (l1_idx << 20), l1_desc);
			} else if (l1_type == 2) {
				l1_sec_t *l1_sec_desc = (l1_sec_t *) (&l1_desc);
				uint32_t l1_pointed_pa_add = START_PA_OF_SECTION(l1_sec_desc);
				uint32_t ap = GET_L1_AP(l1_sec_desc);

				if ((l1_pointed_pa_add & sec_mask) == (pa & sec_mask)) {
					printf("   The L1 in 0x%x (index %x) points to 0x%x\n", START_PA_OF_BLOCK(i), l1_idx, pa);
					printf("      va is %x ap=%d xn=%d, desc = 0x%x\n", (l1_idx << 20), ap, l1_sec_desc->xn, l1_desc);

					if (ap == 3) {
						number_of_l1 += 1;
					}
				}
			}
		}
	}
	printf("   number of L1s = %d\n", number_of_l1);
	printf("   block ref cnt = %d\n", bft_entry_pg->refcnt);
	printf("   block x-ref cnt = %d\n", bft_entry_pg->x_refcnt);
}

extern uint32_t *slpt_va;

void print_all_pointing_L2(uint32_t pa, uint32_t mask)
{
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

//		for (l2_idx = 0; l2_idx < 512; l2_idx += 1) {	
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
}
