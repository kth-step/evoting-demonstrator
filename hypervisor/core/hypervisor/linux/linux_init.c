#include "linux_signal.h"
#include "hyper_config.h"
#include "hyper.h"
#include "mmu.h"
#include "dmmu.h"

extern uint32_t *flpt_va;
extern uint32_t *slpt_va;

extern uint32_t l2_index_p;
extern virtual_machine *curr_vm;

/*We copy the signal codes to the vector table that Linux uses here */

const unsigned long sigreturn_codes[7] = {
	MOV_R7_NR_SIGRETURN, SWI_SYS_SIGRETURN, SWI_THUMB_SIGRETURN,
	MOV_R7_NR_RT_SIGRETURN, SWI_SYS_RT_SIGRETURN, SWI_THUMB_RT_SIGRETURN,
};

const unsigned long syscall_restart_code[2] = {
	SWI_SYS_RESTART,	/* swi  __NR_restart_syscall */
	0xe49df004,		/* ldr  pc, [sp], #4 */
};

void clear_linux_mappings()	//Not called.
{
	uint32_t PAGE_OFFSET = curr_vm->guest_info.page_offset;
	uint32_t VMALLOC_END = curr_vm->guest_info.vmalloc_end;
	uint32_t guest_size = curr_vm->guest_info.guest_size;
	uint32_t MODULES_VADDR =
	    (curr_vm->guest_info.page_offset - 16 * 1024 * 1024);
	uint32_t address;

	uint32_t offset = 0;
	uint32_t *pgd = flpt_va;

	/*
	 * Clear out all the mappings below the kernel image. Maps
	 */
	for (address = 0; address < MODULES_VADDR; address += 0x200000) {
		offset = address >> 21;	//Clear pages 2MB at time
		pgd[offset] = 0;
		pgd[offset + 1] = 0;
		COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, pgd);
	}

	for (; address < PAGE_OFFSET; address += 0x200000) {
		offset = address >> 21;
		pgd[offset] = 0;
		pgd[offset + 1] = 0;
		COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, pgd);
	}

	/*
	 * Clear out all the kernel space mappings, except for the first
	 * memory bank, up to the end of the vmalloc region.
	 */
	if (VMALLOC_END > HAL_VIRT_START)
		hyper_panic("Cannot clear out hypervisor page\n", 1);

	for (address = PAGE_OFFSET + guest_size; address < VMALLOC_END;
	     address += 0x200000) {
		offset = address >> 21;
		pgd[offset] = 0;
		pgd[offset + 1] = 0;
		COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, pgd);
	}
}

#define number_of_1to1_l2s (curr_vm->config->firmware->psize >> 20)
#define pa_in_kernel_code_and_init(pa) (pa < curr_vm->config->firmware->pstart + (curr_vm->config->init_kernel_ex_va_top - curr_vm->config->firmware->vstart))
#define pa_in_kernel_code(pa) (pa < curr_vm->config->firmware->pstart + (curr_vm->config->runtime_kernel_ex_va_top - curr_vm->config->firmware->vstart))

//Unmaps Linux virtual memory in regions [0x0000_0000, 0xC000_0000) and all
//virtual addresses starting from the end of the linearly mapped virtual address
//space until the end of the vmalloc region.
//
//All 4kB blocks (512 entries PTE entries each for ARM Linux) that are not
//mapping executable Linux code up to 0xC07C8000 (0x007C_0000 first code which
//follows the page tables, which is 7MB + 12*2^4kB = 7MB + 192kB), are remapped
//as execute never.
//
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//BUG: NO TLB/CACHE FLUSH!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
dmmu_clear_linux_mappings()
{
hyper_panic("Hypervisor: dmmu_clear_linux_mappings invoked.\n", 1);
	addr_t guest_vstart = curr_vm->config->firmware->vstart;	//0xC000_0000.
	addr_t guest_psize = curr_vm->config->firmware->psize;		//0x0700_0000.
	uint32_t address;
	//0xFF80_0000 is standard unless paravirtualized to make room for page
	//tables after Linux?.
	uint32_t VMALLOC_END = curr_vm->guest_info.vmalloc_end;

	/*
	 * Clear out all the mappings below the kernel image.
	 */

	//Clears all MBs below 0xC000_0000.
	for (address = 0; address < guest_vstart; address += SECTION_SIZE) {
		dmmu_unmap_L1_pageTable_entry(address);
	}

	/*
	 * Clear out all the kernel space mappings, except for the first
	 * memory bank, up to the end of the vmalloc region.
	 */
	if (VMALLOC_END > HAL_VIRT_START)
		hyper_panic("Cannot clear out hypervisor page\n", 1);

	//Clears all MBs in starting from the end of the linearly mapped virtual
	//address space until the end of the vmalloc region.
	for (address = guest_vstart + guest_psize; address < VMALLOC_END; address += SECTION_SIZE) {
		dmmu_unmap_L1_pageTable_entry(address);
	}

	// Remove the executable flag from all L2 used for the 1-to-1 mapping
	// if it is pointing outside the Linux TEXT (+ init?)
	uint32_t l2block;
	//Goes through number_of_1to1_l2s / 2 =
	//(curr_vm->config->firmware->psize >> 20) / 2 =
	//112 / 2 = 56 4kB pages of page tables are processed, with 512 ARM Linux
	//entries in each 4kB page.
	//For all 56*512*4kB = 56*2MB = 112MB = Linux memory mapped by level-2 page
	//tables, all 4kB blocks that are not mapping executable Linux code up to
	//0xC07C8000 (0x007C_0000 first code which follows the page tables, which is
	//7MB + 12*2^4kB = 7MB + 192kB), are remapped as execute never.
	for (l2block = 0; l2block < number_of_1to1_l2s / 2; l2block++) {
		//All 4kB level-2 blocks starting after the physical memory region allocated to Linux:
		//-curr_vm->config->firmware->pstart = 0x8100_0000
		//-curr_vm->config->pa_initial_l2_offset = 0x0700_0000
		//These are the reserved level-2 page tables that consistute 1MB that is cleared by linux_init_dmmu.
		uint32_t l2_base_pa = curr_vm->config->firmware->pstart + curr_vm->config->pa_initial_l2_offset + (l2block << 12);
		//Virtual address of reserved level-2 page tables used by the hypervisor
		//to access Linux memory.
		uint32_t l2_base_va = mmu_guest_pa_to_va(l2_base_pa, curr_vm->config);
		uint32_t l2_idx;
		for (l2_idx = 0; l2_idx < 512; l2_idx++) {
			uint32_t l2_desc_va = l2_base_va + l2_idx*4;	//Byte address of next level-2 descriptor.
			uint32_t l2_desc = *((uint32_t *) l2_desc_va);	//Read level-2 descriptor.
			uint32_t l2_type = l2_desc & DESC_TYPE_MASK;	//DESC_TYPE_MASK = 0b11.

			if ((l2_type != 2) && (l2_type != 3))		//Not small 4kB page descriptor. That is, invalid or large page.
				continue;
														//Small page with or without xn.
			l2_small_t *pg_desc = (l2_small_t *) (&l2_desc);
			//Obtains the aboslute physical address of the 4kB page pointed to
			//by the level-2 descriptor.
			uint32_t l2_pointed_pa = START_PA_OF_SPT(pg_desc);
			uint32_t ap = GET_L2_AP(pg_desc);

			//Level-2 descriptor points to physical 4kB page that belongs to
			//executable memory within init_kernel_ex_va_top.
			if (pa_in_kernel_code_and_init(l2_pointed_pa))
				continue;

			if (pg_desc->xn)	//Not exectuable memory.
				continue;

			//Marks descriptor with index l2_idx of level-2 page table at
			//l2_base_pa as unmapped.
			dmmu_l2_unmap_entry(l2_base_pa, l2_idx);
			//Maps descriptor with index l2_idx of level-2 page table at
			//l2_base_pa to physical 4kB page at l2_pointed_pa as execute never
			//(bit 0).
			dmmu_l2_map_entry(l2_base_pa, l2_idx, l2_pointed_pa, l2_desc | 0b1);
		}		
	}
}

uint32_t hypercall_linux_init_end() {
	// Remove the executable flag from all L2 used for the 1-to-1 mapping
	// if it is pointing outside the Linux TEXT (+ init?)
	uint32_t l2block;
	//number_of_1to1_l2s / 2 = (curr_vm->config->firmware->psize >> 20) / 2 =
	//112 / 2 = 56 4kB pages of page tables are processed, with 512 ARM Linux
	//entries in each 4kB page.
	for (l2block = 0; l2block < number_of_1to1_l2s / 2; l2block++) {
		uint32_t l2_base_pa = curr_vm->config->firmware->pstart + curr_vm->config->pa_initial_l2_offset + (l2block << 12);
		uint32_t l2_base_va = mmu_guest_pa_to_va(l2_base_pa, curr_vm->config);
		uint32_t l2_idx;
		for (l2_idx = 0; l2_idx < 512; l2_idx++) {
			uint32_t l2_desc_va = l2_base_va + l2_idx*4;
			uint32_t l2_desc = *((uint32_t *) l2_desc_va);
			uint32_t l2_type = l2_desc & DESC_TYPE_MASK;

			if ((l2_type != 2) && (l2_type != 3))
				continue;

			l2_small_t *pg_desc = (l2_small_t *) (&l2_desc);
			uint32_t l2_pointed_pa = START_PA_OF_SPT(pg_desc);
			uint32_t ap = GET_L2_AP(pg_desc);
			if (pa_in_kernel_code(l2_pointed_pa))
				continue;

			if (pg_desc->xn)
				continue;
			//Marks descriptor with index l2_idx of level-2 page table at
			//l2_base_pa as unmapped.
			dmmu_l2_unmap_entry(l2_base_pa, l2_idx);
			//Maps descriptor with index l2_idx of level-2 page table at
			//l2_base_pa to physical 4kB page at l2_pointed_pa.
			dmmu_l2_map_entry(l2_base_pa, l2_idx, l2_pointed_pa, l2_desc | 0b1);
		}		
	}
	return 0;
}

void init_linux_sigcode()
{
	memcpy((void *)KERN_SIGRETURN_CODE, sigreturn_codes,
	       sizeof(sigreturn_codes));
	memcpy((void *)KERN_RESTART_CODE, syscall_restart_code,
	       sizeof(syscall_restart_code));
}

void init_linux_page()	//NOT INVOKED!!!
{
	uint32_t *p, i;

	/*Map the first pages for the Linux kernel OS specific
	 * These pages must cover the whole boot phase before the setup arch
	 * in Linux, in case of built in Ramdisk its alot bigger*/

	uint32_t linux_phys_ram = HAL_PHYS_START + 0x1000000;
	pt_create_coarse(flpt_va, 0xc0000000, linux_phys_ram, 0x100000,
			 MLT_USER_RAM);

	for (i = 1; i < 0x50; i++) {
		pt_create_section(flpt_va, 0xC0000000 + (i * (1 << 20)),
				  linux_phys_ram + i * (1 << 20), MLT_USER_RAM);
	}

	uint32_t phys = 0;
	p = (uint32_t *) ((uint32_t) slpt_va + ((l2_index_p - 1) * 0x400));	/*256 pages * 4 bytes for each lvl 2 page descriptor */
	/*Modify the master swapper page global directory to read only */

	/*Maps first eight pages 0-0x8000 */
	for (i = 0x4; i < 0x8; i++, phys += 0x1000) {
		p[i] &= PAGE_MASK;
		/*This maps Linux kernel pages to the hypervisor and sets it read only */
		p[i] |= (uint32_t) (GET_PHYS(flpt_va) + phys);

		p[i] &= ~(MMU_L2_SMALL_AP_MASK << MMU_L2_SMALL_AP_SHIFT);
		p[i] |= (MMU_AP_USER_RO << MMU_L2_SMALL_AP_SHIFT);	//READ only
	}
}

//uint32_t linux_l2_index_p = 0;
uint32_t linux_l2_index_p = 2;

//Get physical address of next level-2 page table of 1kB, which is in reserved
//memory after the Linux allocated memory at
//curr_vm->config->firmware->pstart + curr_vm->config->pa_initial_l2_offset.
addr_t linux_pt_get_empty_l2()
{
	//pa_l2_pt = 0x8100_0000 + 0x0700_0000 = 0x8800_0000.
	uint32_t pa_l2_pt = curr_vm->config->firmware->pstart + curr_vm->config->pa_initial_l2_offset;
	//Gives the virtual address of pa_l2_pt in the window
	//[0xE8000000, 0xEF00_0000) used by the hypervisor to access Linux memory.
	uint32_t va_l2_pt = mmu_guest_pa_to_va(pa_l2_pt, curr_vm->config);
	//SECTION_SIZE = 0x00100000 = 2^20
	//0x400 = 1024 = 2^10.
	//linux_l2_index_p is at most 2^10+4.
	//At most 2^10 = 1024 L2 tables spans
	//1024 * 256 L2 entries * 4kB per L2 entry = 1GB.
	//Only one MB is reserved for page tables after the memory allocated for Linux.
	if ((linux_l2_index_p * 0x400) > SECTION_SIZE) {	// Set max size of L2 pages
		printf("No more space for more L2s\n");
		while (1) ;	//hang
		return 0;
	} else {
		//Each L2 table is 0x400 Bytes = 1024 Bytes = 1kB = 256 level-2 desctiptors.
		addr_t index = linux_l2_index_p * 0x400;
		// memset((uint32_t *) ((uint32_t) va_l2_pt + index), 0, 0x400);
		//Physical address of L2 table, 1kB aligned.
		uint32_t l2_base_add = (uint32_t) (pa_l2_pt + index);

		// assuming that va_l2_pt is 4kb aligned
		//Increment global pointer.
		linux_l2_index_p++;
//		if ((linux_l2_index_p & 0x2) == 0x2)						//If pointer has passed two page tables, increment it by two
//			linux_l2_index_p = (linux_l2_index_p & (~0x3)) + 4;		//more, since linux uses two page tables more for metadata.
		if ((linux_l2_index_p & 0x3) == 0x0)						//Multiple of four. Increment by two to get to the hardware
			linux_l2_index_p = linux_l2_index_p + 2;				//page tables, skipping the Linux meta data.

//printf("linux_pt_get_empty_l2: 0x%x\n", l2_base_add);
		return l2_base_add;
	}
}

#define MAP_LINUX_USING_L2
#define LINUX_5_15_13
//Clears the first MB after Linux allocated memory (112MB) where level-2 page
//tables are stored by accessing the virtual address space that the hypervisor
//use to access Linux memory.
//
//Updates DMMU data structures for the first 16 Linux PTE level-2 page tables
//(each containing 512 level-2 descriptors), which map 32MB. These level-2 page
//tables are reserved for WHAT???
//
//Configures level-2 page tables to map the 112MB of Linux for the identity
//mapping used by Linux during boot and the virtual mapping used by Linux after
//configuring the MMU:
//-Boot: [0x8110_0000, 0x8800_0000) -> [0x8110_0000, 0x8800_0000) (Linux uses
// sections but only level-2 pages are used by DMMU.)
//-After MMU enabled: [0xC010_0000, 0xC700_0000) -> [0x8110_0000, 0x8800_0000)
// (Linux uses a mix of sections and small pages depending on how much memory is
// mapped.)
//by obtaining new level-2 page tables located in the region following the
//memory allocated to Linux (0x8800_0000) and updating DMMU data structures
//accordingly, configuring the level-1 table to point to the obtained level-2
//page tables, and configuring the obtained level-2 page tables to map the 4kB
//pages accordingly.
//
//Summary:
//Configures page tables to map all physically allocated Linux memory (112MB) as
//an identity mapping for boot up to arch/arm/kernel/head.S:__create_page_tables
//and as the linear virtual mapping setup by
//arch/arm/kernel/head.S:__create_page_tables.
#ifndef LINUX_5_15_13	//Linux 3.10.
void linux_init_dmmu()
{
	uint32_t error;
	uint32_t sect_attrs, sect_attrs_ro, small_attrs, small_attrs_ro, small_attrs_xn, page_attrs, table2_idx, i;
	addr_t table2_pa;
	//First address of guest in virtual address space = 0xC000_0000.
	addr_t guest_vstart = curr_vm->config->firmware->vstart;
	//First address of guest in physical address space = 0x8100_0000.
	addr_t guest_pstart = curr_vm->config->firmware->pstart;
	//Physical memory size allocated to Linux = 0x0700_0000 (see guest_data.S).
	addr_t guest_psize = curr_vm->config->firmware->psize;
	printf("Linux mem info %x %x %x\n", guest_vstart, guest_pstart, guest_psize);
	/*Linux specific mapping */
	/*Section page with user RW in kernel domain with Cache and Buffer */
	sect_attrs = MMU_L1_TYPE_SECTION;
	sect_attrs |= MMU_AP_USER_RW << MMU_SECTION_AP_SHIFT;
	sect_attrs |= (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
	sect_attrs |= (MMU_FLAG_B | MMU_FLAG_C);

	sect_attrs_ro = MMU_L1_TYPE_SECTION;
	sect_attrs_ro |= MMU_AP_USER_RO << MMU_SECTION_AP_SHIFT;
	sect_attrs_ro |= (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
	sect_attrs_ro |= (MMU_FLAG_B | MMU_FLAG_C);

	/*L1PT attrs */
	page_attrs = MMU_L1_TYPE_PT;
	page_attrs |= (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);

	/*Small page with CB on and RW */
	small_attrs = MMU_L2_TYPE_SMALL;
	small_attrs |= (MMU_FLAG_B | MMU_FLAG_C);
	small_attrs_ro |= small_attrs | (MMU_AP_USER_RO << MMU_L2_SMALL_AP_SHIFT);
	small_attrs |= MMU_AP_USER_RW << MMU_L2_SMALL_AP_SHIFT;
	small_attrs_xn = small_attrs | 0b1;

	// clear the memory reserved for L2s
	//pa_initial_l2_offset = psize = 0x0700_0000.
	//guest_pstart = 0x8100_0000.
	//reserved_l2_pts_pa = physical end address of Linux = 0x8800_0000 where
	//level-2 page tables are stored.
	addr_t reserved_l2_pts_pa = curr_vm->config->pa_initial_l2_offset + guest_pstart;
	/*Set whole 1MB reserved address region in Linux as L2_pt */
	//reserved_l2_pts_pa - pstart + 0xE800_0000 =
	//0x8800_0000 - 0x8100_0000 + 0xE800_0000 =
	//0x0700_0000 + 0xE800_0000 =
	//0xEF00_0000 =
	//virtual address used by the hypervisor to access Linux memory, where
	//level-2 page tables are stored.
	addr_t reserved_l2_pts_va = mmu_guest_pa_to_va(reserved_l2_pts_pa, curr_vm->config);

	/*Memory setting the reserved L2 pages to 0
	 *We clean not the whole MB   */
	//Clear the 4096 1kB page tables (each mapping 1MB, total coverage 4GB; size
	//of 4096 1kB is 4MB; 4096 1kB page tables fit in 1024 4kB pages) starting
	//after allocated Linux physical memory.
	memset((addr_t *) reserved_l2_pts_va, 0, 0x100000);
//printf("LINUX_INIT: reserved_l2_pts_pa = %x\n", reserved_l2_pts_pa);
//printf("LINUX_INIT: reserved_l2_pts_va = %x\n", reserved_l2_pts_va);

	//ARM linux uses 512 level-2 descriptors = 2kB plus 2kB metadata in each
	//page, therefore iterating  with i at a PAGE_SIZE = 4kB granularity.
	//This loop processes Linux PTEs taking 0x0001_0000 = 64kB, with each PTE
	//being 4kB = 0x0000_1000. This loop covers 16 such level-2 pages since
	//0x0000_1000*0x10 = 0x0000_1000 * 2^4 = 0x0000_1000 << 4 = 0x0001_0000.
	//512 level-2 ARM Linux descriptors per PTE *
	//each level-2 descriptor mapping 4kB * 16 PTEs =
	//512*4*1024*16 bytes mapped =
	//1024*2*1024*16 bytes mapped =
	//1024*1024*32 bytes mapped =
	//1MB*32 bytes mapped =
	//32MB mapped.
	//Should be more than 32MB??????????????????????????????????????????????????
	for (i = reserved_l2_pts_pa; i < reserved_l2_pts_pa + 0x10000; i += PAGE_SIZE) {
		//Reads 512 level-2 descriptor requiring 2kB memory and updates DMMU
		//data structures accordingly.
		if ((error = dmmu_create_L2_pt(i)))
			printf("\n\tCould not map L2 PT: %d %x\n", error, i);
	}
	

	uint32_t offset;
	/*Can't map from offset = 0 because start addresses contains page tables */
	/*Maps PA-PA for boot */

#ifndef MAP_LINUX_USING_L2	//IS DEFINED SO THIS CLAUSE IS NOT COMPILED!
	for (offset = SECTION_SIZE; offset + SECTION_SIZE <= guest_psize; offset += SECTION_SIZE) {
		dmmu_map_L1_section(guest_pstart + offset, guest_pstart + offset, sect_attrs);
	}
	/*Maps VA-PA for kernel */
	for (offset = SECTION_SIZE; offset + SECTION_SIZE <= (guest_psize - SECTION_SIZE * 16); offset += SECTION_SIZE) {
		dmmu_map_L1_section(guest_vstart + offset, guest_pstart + offset, sect_attrs);
	}
	/*Map last 16MB as coarse */
	for (; offset + SECTION_SIZE <= guest_psize; offset += SECTION_SIZE) {
		table2_pa = linux_pt_get_empty_l2();	/*pointer to private L2PTs in guest */
		if ((error = dmmu_l1_pt_map((addr_t) guest_vstart + offset, table2_pa, page_attrs)))
			printf("\n\tCould not map L1 PT in set PMD: %d\n", error);

		/*Get index of physical L2PT */
		table2_idx = (table2_pa - (table2_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT;
		table2_idx *= 0x100;	/*256 pages per L2PT */
		uint32_t end = table2_idx + 0x100;
		uint32_t page_pa;
		for (i = table2_idx, page_pa = offset; i < end; i++, page_pa += 0x1000) {
			if (dmmu_l2_map_entry(table2_pa, i, page_pa + guest_pstart, small_attrs))
				printf("\n\tCould not map L2 entry in new pgd\n");
		}

	}
#else	//IS DEFINED SO THIS CLAUSE IS COMPILED!
	//SECTION_SIZE = 0x00100000 = 1MB
	//PSIZE (guest_data.S defines psize to 0x07000000 = 112MB).
	//Maps all 112MB Linux memory except the first MB = 111MB =
	//0x07000000 - 0x0010_0000 = 0x06F0_0000 physical memory of Linux starting
	//at 0x8110_0000:
	//
	//Last is offset = 0x06F0_0000 (since limit is
	//offset + SECTION_SIZE <= guest_psize which is equivalent to
	//offset < guest_psize = 0x0700_0000), meaning index of last MB is
	//0x0700_0000 - 0x0010_0000 = 0x06F0_0000.
	//Identity mapping for Linux boot which assumes no MMU:
	//[0x8110_0000, 0x8110_0000 + 0x06F0_0000) -> [0x8110_0000, 0x8110_0000 + 0x06F0_0000) =
	//[0x8110_0000, 0x8800_0000) -> [0x8110_0000, 0x8800_0000)
	//Virtual mapping for Linux which has configured MMU:
	//[0xC010_0000, 0xC010_0000 + 0x06F0_0000) -> [0x8110_0000, 0x8110_0000 + 0x06F0_0000) =
	//[0xC010_0000, 0xC700_0000) -> [0x8110_0000, 0x8800_0000)
	for (offset = SECTION_SIZE; offset + SECTION_SIZE <= guest_psize; offset += SECTION_SIZE) {
		//Physical address of 1kB level-2 page table not in use with 256
		//entries. 1kB aligned.
		table2_pa = linux_pt_get_empty_l2(); /*pointer to private L2PTs in guest*/
		//Updates DMMU data structures to reflect the creation of the new
		//level-2 page table, by considering 512 entries, while only space for
		//256 entries have been reserved. This works since also reading the next
		//level-2 page has no effect since it is zero.
		dmmu_create_L2_pt(table2_pa & L2_BASE_MASK);	//L2_BASE_MASK = 0xFFFF_F000.
		//Makes virtual address guest_pstart + offset mapped by level-2 table at
		//table2_pa, all its entries are unmapped. This is the identity mapping
		//used for Linux boot.
		dmmu_l1_pt_map(guest_pstart + offset, table2_pa, page_attrs);
		//Makes virtual address guest_vstart + offset is mapped by level-2 table
		//at table2_pa, all its entries are unmapped. This is the virtual
		//mapping used for Linux after it has setup its virtual mapping by
		//enabling the MMU, starting at 0xC000_0000.
		dmmu_l1_pt_map(guest_vstart + offset, table2_pa, page_attrs);

//printf("HV, PA-PA: PA=%x->PA=%x	", guest_pstart + offset, guest_pstart + offset);
//printf("HV, VA-PA: VA=%x->PA=%x\n", guest_vstart + offset, guest_pstart + offset);

		//L2_BASE_MASK = 0xFFFF_F000 = clears 12 LSBs.
		//MMU_L1_PT_SHIFT = 10.
		//table2_pa is 1kB aligned. Gets [0,3] index of table2_pa.
		table2_idx = (table2_pa - (table2_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT;
		//[0, 0x100, 0x200, 0x300] = [0, 256, 512, 768].
		table2_idx *= 0x100; /*256 pages per L2PT*/
		//0x100 = 256. Gives [256, 512, 768, 1024].
		uint32_t end = table2_idx + 0x100;
		//Current 1MB physical block to be mapped by a virtual address.
		uint32_t page_pa = guest_pstart + offset;

//printf("HV: table2_idx = %x\n", table2_idx);

		//For each level-2 descriptor of the current level-2 table (table2_pa;
		//256 entries, each mapping a page of 4kB = 0x1000 bytes).
		//Maps all 256 4kB blocks of the current MB.
		for(i = table2_idx; i < end; i++, page_pa += 0x1000) {
			// Do not map executable the part of the memory above .text and .init of linux

			//Maps level-2 entry at i-th index of level-2 page table at physical
			//address table2_pa to physical 4kB page at page_pa.
			if (page_pa <= guest_pstart + (curr_vm->config->initial_kernel_ex_va_top - guest_vstart))	//Executable code.
				//page table at physical address table2_pa maps to page with
				//physical address page_pa = guest_pstart + offset + m*0x0000_1000
				dmmu_l2_map_entry(table2_pa, i, page_pa, small_attrs);
			else {																	//Not executable code.
				dmmu_l2_map_entry(table2_pa, i, page_pa, small_attrs_xn);
				dmmu_entry_t *e = get_bft_entry_by_block_idx(page_pa >> 12);
				if (e->x_refcnt > 0)
					printf("\t %x ref_xnt > 0 %d\n", (page_pa >> 12), e->x_refcnt);
			}
		}
	}
#endif


#if 1				//Linux 3.10
	/*New ATAG (3.10) at end of image */

	//NOT NEEDED????????????????????????????????????????????????????????????????
	//??????????????????????????????????????????????????????????????????????????
	//??????????????????????????????????????????????????????????????????????????
	//??????????????????????????????????????????????????????????????????????????
	//??????????????????????????????????????????????????????????????????????????
	//??????????????????????????????????????????????????????????????????????????
	//Makes 0x9FE00000 mapped to 1MB section at physical address 0x9FE00000.
//	dmmu_map_L1_section(0x9FE00000, 0x9FE00000, sect_attrs);
	//dmmu_map_L1_section(0xFA400000, 0x87000000, sect_attrs);
#endif
	/*special mapping for start address */
	//Get physical address of next L2 page table of 1kB.
	table2_pa = linux_pt_get_empty_l2();	/*pointer to private L2PTs in guest */
	//Reads 512 level-2 descriptors stored in 2kB memory and updates DMMU data
	//structures accordingly.
	dmmu_create_L2_pt(table2_pa);
	//Physical address guest_pstart is mapped by level-2 table at
	//table2_pa. This is the identity mapping used for Linux boot.
	dmmu_l1_pt_map(guest_pstart, table2_pa, page_attrs);
	//Virtual address guest_vstart is mapped by level-2 table at
	//table2_pa. This is the virtual mapping used for Linux after it has setup
	//its virtual mapping by enabling the MMU, starting at 0xC000_0000.
	dmmu_l1_pt_map(guest_vstart, table2_pa, page_attrs);

//printf("guest_init2, HV, PA-PA: PA=%x->PA=%x\n", guest_pstart, guest_pstart);
//printf("guest_init2, HV, VA-PA: VA=%x->PA=%x, END=%x\n", guest_vstart, guest_pstart, guest_pstart + 0x200000);

	//Physical start address of guest, only first kB is used.
	uint32_t page_pa = guest_pstart;	//0x8100_000.

	//table2_pa is 1kB aligned. Gets [0,3] index of table2_pa.
	table2_idx = (table2_pa - (table2_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT;
	//0, 0x100, 0x200, or 0x300 = 0, 256, 512, or 768.
	table2_idx *= 0x100; /*256 pages per L2PT*/
	//0x100, 0x200, 0x300, or 0x400 = 256, 512, 768, or 1024.
	uint32_t end = table2_idx + 0x100;
	//Iterates over all 256 entries of the level-2 page table at table2_pa to
	//the 256 consecutive 4kB blocks (1MB contiguous memory) starting at the
	//start of the guest page_pa = guest_pstart.
	for(i = table2_idx; i < end; i++, page_pa+=0x1000) {
   		if ((i % 256) >= 4 && (i % 256) <= 7) {
			//Read-only for unprivileged Linux.
			uint32_t ro_attrs = 0xE | (MMU_AP_USER_RO << MMU_L2_SMALL_AP_SHIFT);
			//Maps level-2 entry at i-th index of level-2 page table at physical
			//address table2_pa to physical 4kB page at page_pa.
			dmmu_l2_map_entry(table2_pa, i, page_pa, ro_attrs);
		} else
			dmmu_l2_map_entry(table2_pa, i, page_pa, small_attrs);
	}
}
#else /* For Linux 5.15.13 */
//Setups identity mapping for access Linux.
void linux_init_dmmu()
{
	uint32_t error;
	uint32_t sect_attrs, sect_attrs_ro, small_attrs;
	uint32_t small_attrs_xn, page_attrs, table2_idx, i;
	addr_t table2_pa;
	//First address of guest in virtual address space = 0xC000_0000.
	addr_t guest_vstart = curr_vm->config->firmware->vstart;
	//First address of guest in physical address space = 0x8100_0000.
	addr_t guest_pstart = curr_vm->config->firmware->pstart;
	//Physical memory size allocated to Linux = 0x0700_0000 (see guest_data.S).
	addr_t guest_psize = curr_vm->config->firmware->psize;
	printf("Linux 5.15.13 mem info %x %x %x\n", guest_vstart, guest_pstart, guest_psize);
	/*Linux specific mapping */
	/*Section page with user RW in kernel domain with Cache and Buffer */
	sect_attrs = MMU_L1_TYPE_SECTION;
	sect_attrs |= MMU_AP_USER_RW << MMU_SECTION_AP_SHIFT;
	sect_attrs |= (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
	sect_attrs |= (MMU_FLAG_B | MMU_FLAG_C);

	sect_attrs_ro = MMU_L1_TYPE_SECTION;
	sect_attrs_ro |= MMU_AP_USER_RO << MMU_SECTION_AP_SHIFT;
	sect_attrs_ro |= (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);
	sect_attrs_ro |= (MMU_FLAG_B | MMU_FLAG_C);

	/*L1PT attrs */
	page_attrs = MMU_L1_TYPE_PT;
	page_attrs |= (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);

	/*Small page with CB on and RW */
	small_attrs = MMU_L2_TYPE_SMALL;
	small_attrs |= (MMU_FLAG_B | MMU_FLAG_C);
	small_attrs |= MMU_AP_USER_RW << MMU_L2_SMALL_AP_SHIFT;
	small_attrs_xn = small_attrs | 0b1;

	// clear the memory reserved for L2s
	//pa_initial_l2_offset = psize = 0x0700_0000.
	//guest_pstart = 0x8100_0000.
	//reserved_l2_pts_pa = physical end address of Linux = 0x8800_0000 where
	//level-2 page tables are stored.
	addr_t reserved_l2_pts_pa = curr_vm->config->pa_initial_l2_offset + guest_pstart;
	/*Set whole 1MB reserved address region in Linux as L2_pt */
	//reserved_l2_pts_pa - pstart + 0xE800_0000 =
	//0x8800_0000 - 0x8100_0000 + 0xE800_0000 =
	//0x0700_0000 + 0xE800_0000 =
	//0xEF00_0000 =
	//virtual address used by the hypervisor to access Linux memory, where
	//level-2 page tables are stored.
	addr_t reserved_l2_pts_va = mmu_guest_pa_to_va(reserved_l2_pts_pa, curr_vm->config);

	/*Memory setting the reserved L2 pages to 0
	 *We clean not the whole MB   */
	//Clear the 4096 1kB page tables (each mapping 1MB, total coverage 4GB; size
	//of 4096 1kB is 4MB; 4096 1kB page tables fit in 1024 4kB pages) starting
	//after allocated Linux physical memory.
	memset((addr_t *) reserved_l2_pts_va, 0, 0x100000);

	//1MB = 1024 level-2 page tables. Each page table contains 256 entries, each
	//entry covering 4kB. 1MB of level-2 page tables covers 1024*256*4kB = 1GB.
/*	Not needed since dmmu_create_L2_pt is invoked in the loop below.
	for (i = reserved_l2_pts_pa; i < reserved_l2_pts_pa + 0x10000; i += PAGE_SIZE) {
		//Reads 512 level-2 descriptor requiring 2kB memory and updates DMMU
		//data structures accordingly.
		if ((error = dmmu_create_L2_pt(i)))
			printf("\n\tCould not map L2 PT: %d %x\n", error, i);
	}
*/
	uint32_t ret;

	/*special mapping for start address */
	//Get physical address of next L2 page table of 1kB.
	table2_pa = linux_pt_get_empty_l2();	/*pointer to private L2PTs in guest */
	//Reads 512 level-2 descriptors stored in 2kB memory and updates DMMU data
	//structures accordingly.
	ret = dmmu_create_L2_pt(table2_pa & L2_BASE_MASK);
	if (ret) {
		printf("Hypervisor initialization5: table2_pa = 0x%x, ret = 0x%x\n", table2_pa, ret);
		while (1);
	}
	//Physical address guest_pstart is mapped by level-2 table at
	//table2_pa. This is the identity mapping used for Linux boot.
	ret = dmmu_l1_pt_map(guest_pstart, table2_pa, page_attrs);
	if (ret) {
		printf("Hypervisor initialization6: table2_pa = 0x%x, ret = 0x%x\n", table2_pa, ret);
		while (1);
	}

	//Physical start address of guest, only first kB is used.
	uint32_t page_pa = guest_pstart;	//0x8100_0000.

	//table2_pa is 1kB aligned. Gets [2,3] index of table2_pa.
	table2_idx = (table2_pa - (table2_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT;
	//0x200, or 0x300 = 512, or 768.
	table2_idx *= 256; /*256 pages per L2PT*/
	//0x300, or 0x400 = 768, or 1024.
	uint32_t end = table2_idx + 256;
	//Iterates over all 256 entries of the level-2 page table at table2_pa to
	//the 256 consecutive 4kB blocks (1MB contiguous memory) starting at the
	//start of the guest page_pa = guest_pstart.
	for(i = table2_idx; i < end; i++, page_pa += 0x1000) {
   		if ((i % 256) >= 4 && (i % 256) <= 7) {
			//Read-only for unprivileged Linux for page tables.
			uint32_t ro_attrs = 0xE | (MMU_AP_USER_RO << MMU_L2_SMALL_AP_SHIFT);
			//Maps level-2 entry at i-th index of level-2 page table at physical
			//address table2_pa to physical 4kB page at page_pa.
			ret = dmmu_l2_map_entry(table2_pa, i, page_pa, ro_attrs);
			if (ret) {
				printf("Hypervisor initialization7: table2_pa = 0x%x, ret = 0x%x, i = %d\n", table2_pa, ret, i);
				while (1);
			}
		} else {
			ret = dmmu_l2_map_entry(table2_pa, i, page_pa, small_attrs);
			if (ret) {
				printf("Hypervisor initialization8: table2_pa = 0x%x, ret = 0x%x, i = %d\n", table2_pa, ret, i);
				while (1);
			}
		}
	}

	uint32_t offset;
	/*Can't map from offset = 0 because start addresses contains page tables */
	/*Maps PA-PA for boot */

	//SECTION_SIZE = 0x00100000 = 1MB
	//PSIZE (guest_data.S defines psize to 0x07000000 = 112MB).
	//Maps all 112MB Linux memory except the first MB = 111MB =
	//0x07000000 - 0x0010_0000 = 0x06F0_0000 physical memory of Linux starting
	//at 0x8110_0000:
	//
	//Last is offset = 0x06F0_0000 (since limit is
	//offset + SECTION_SIZE <= guest_psize which is equivalent to
	//offset < guest_psize = 0x0700_0000), meaning index of last MB is
	//0x0700_0000 - 0x0010_0000 = 0x06F0_0000.
	//Identity mapping for Linux boot which assumes no MMU:
	//[0x8110_0000, 0x8110_0000 + 0x06F0_0000) -> [0x8110_0000, 0x8110_0000 + 0x06F0_0000) =
	//[0x8110_0000, 0x8800_0000) -> [0x8110_0000, 0x8800_0000)
	//Virtual mapping for Linux which has configured MMU:
	//[0xC010_0000, 0xC010_0000 + 0x06F0_0000) -> [0x8110_0000, 0x8110_0000 + 0x06F0_0000) =
	//[0xC010_0000, 0xC700_0000) -> [0x8110_0000, 0x8800_0000)
	for (offset = SECTION_SIZE; offset + SECTION_SIZE <= guest_psize; offset += SECTION_SIZE) {
		//Physical address of 1kB level-2 page table not in use with 256
		//entries. 1kB aligned.
		table2_pa = linux_pt_get_empty_l2(); /*pointer to private L2PTs in guest*/
		uint32_t l2_pa = pa_to_l2_base_pa(guest_pstart + offset);

if (table2_pa != l2_pa) {
printf("Hypervisor linux_init.c: pa_to_l2_base_pa is incorrect: pa = 0x%x, table2_pa = 0x%x, l2_pa = 0x%x.\n", guest_pstart + offset, table2_pa, l2_pa);
while (1);
}

		//Updates DMMU data structures to reflect the creation of the new
		//level-2 page table, by considering 512 entries, while only space for
		//256 entries have been reserved. This works since also reading the next
		//level-2 page has no effect since it is zero.
		ret = dmmu_create_L2_pt(table2_pa & L2_BASE_MASK);	//L2_BASE_MASK = 0xFFFF_F000.
		if (ret != 0 && ret != ERR_MMU_ALREADY_L2_PT) {
			printf("Hypervisor initialization1: table2_pa = 0x%x, ret = 0x%x, offset = 0x%x\n", table2_pa, ret, offset);
			while (1);
		}
		//Makes virtual address guest_pstart + offset mapped by level-2 table at
		//table2_pa, all its entries are unmapped. This is the identity mapping
		//used for Linux boot.
		ret = dmmu_l1_pt_map(guest_pstart + offset, table2_pa, page_attrs);
		if (ret) {
			printf("Hypervisor initialization2: table2_pa = 0x%x, ret = %d, offset = 0x%x\n", table2_pa, ret, offset);
			while (1);
		}

//
//printf("HV Linux init: table2_pa = %x; guest_vstart + offset = %x; offset = %x\n", table2_pa, guest_vstart + offset, offset);
//		dmmu_l1_pt_map(guest_vstart + offset, table2_pa, page_attrs);
//
		//L2_BASE_MASK = 0xFFFF_F000 = clears 12 LSBs.
		//MMU_L1_PT_SHIFT = 10.
		//table2_pa is 1kB aligned. Gets [2,3] index of table2_pa.
		table2_idx = (table2_pa - (table2_pa & L2_BASE_MASK)) >> MMU_L1_PT_SHIFT;
		//[0x200, 0x300] = [512, 768].
		table2_idx *= 0x100; /*256 pages per L2PT*/
		//0x100 = 256. Gives [768, 1024].
		uint32_t end = table2_idx + 0x100;
		//Current 1MB physical block to be mapped by a virtual address.
		uint32_t page_pa = guest_pstart + offset;

		//For each level-2 descriptor of the current level-2 table (table2_pa;
		//256 entries, each mapping a page of 4kB = 0x1000 bytes).
		//Maps all 256 4kB blocks of the current MB.
		for(i = table2_idx; i < end; i++, page_pa += 0x1000) {
			// Do not map executable the part of the memory above .text and .init of linux

			//Maps level-2 entry at i-th index of level-2 page table at physical
			//address table2_pa to physical 4kB page at page_pa.
//			if (page_pa <= guest_pstart + (curr_vm->config->initial_kernel_ex_va_top - guest_vstart)) {	//Executable code.
				//page table at physical address table2_pa maps to page with
				//physical address page_pa = guest_pstart + offset + m*0x0000_1000
//				printf("Hypervisor initialization calls dmmu_l2_map_entry: table2_pa = 0x%x, i = 0x%x, offset = 0x%x\n", table2_pa, i, offset);
				ret = dmmu_l2_map_entry(table2_pa, i, page_pa, small_attrs);
				if (ret) {
					printf("Hypervisor initialization3: table2_pa = 0x%x, ret = 0x%x, offset = 0x%x\n", table2_pa, ret, offset);
					while (1);
				}
/*			} else {																	//Not executable code.
				ret = dmmu_l2_map_entry(table2_pa, i, page_pa, small_attrs_xn);
				if (ret) {
					printf("Hypervisor initialization4: table2_pa = 0x%x, ret = 0x%x, offset = 0x%x\n", table2_pa, ret, offset);
					while (1);
				}
				dmmu_entry_t *e = get_bft_entry_by_block_idx(page_pa >> 12);
				if (e->x_refcnt > 0)
					printf("\t %x ref_xnt > 0 %d\n", (page_pa >> 12), e->x_refcnt);
			}
*/
		}
	}
}
#endif

void linux_init()	//Not invoked.
{
	/*Initalise the page tables for Linux kernel */
	init_linux_page();
	/*Copy the signal codes into the vector table */
	init_linux_sigcode();
}
