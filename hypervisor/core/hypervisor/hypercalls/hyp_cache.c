#include "hw.h"
#include "hyper.h"

/*Cache and TLB operations*/

/*D Cache operations*/
////////
void hypercall_dcache_clean_region(addr_t start, addr_t end)
{
	clean_dcache_region(start, end);
}

////////

////////
void hypercall_dcache_invalidate_region(addr_t start, addr_t end)
{
	inv_dcache_region(start, end);
}

////////

void hypercall_dcache_flush_area(addr_t va, uint32_t size)
{
	mem_cache_dcache_area(va, size, FLUSH);

}

void hypercall_dcache_clean_area(addr_t va, uint32_t size)
{
	mem_cache_dcache_area(va, size, CLEAN);

}

void hypercall_dcache_invalidate_mva(addr_t va)
{

	COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, va);
	dsb();

}

/*I Cache operations*/
void hypercall_icache_invalidate_all()
{
	COP_WRITE(COP_SYSTEM, COP_ICACHE_INVALIDATE_ALL, 0);
}

/*Not implemented, nothing that uses it yet*/
void hypercall_icache_invalidate_mva(addr_t va)
{
	hyper_panic("Not implemented!", 1);
}

void hypercall_branch_invalidate_all()
{
	COP_WRITE(COP_SYSTEM, COP_BRANCH_PRED_INVAL_ALL, 0);
}

void hypercall_flush_all()
{
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);
	mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback
}

/* TLB Operations */

void hypercall_tlb_invalidate_mva(addr_t va)
{
	COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA, va);
}

void hypercall_tlb_invalidate_asid(uint32_t asid)
{
	/*ARM 926 does not have this function */
#if ARM_ARCH > 5
	COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_ASID, asid);
#endif

}

//Flushes (cleans and invalidates) all data caches.
//Includes LoUU, LoC, and LoUIS.
void hypercall_clean_or_invalidate_dcache(void) {
	mem_flush_dcache();
}


void hypercall_clean_ends_invalidate_dma_dcache(uint32_t start_va, uint32_t end_va) {
	uint32_t ctr;
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache1: start_va = 0x%x, end_va = 0x%x\n", start_va, end_va);
	//COP_SYSTEM = p15
	//COP_ID_CACHE_CONTROL_ARMv7_CLIDR = "c0, c0, 1"
	//COP_READ2(cop, op1, func, reg) =
	//asm volatile("mrc " cop "," op1 ", %0, " func : "=r" (reg))
	//COP_READ2(COP_SYSTEM, "0", COP_ID_CACHE_CONTROL_ARMv7_CLIDR, ctr) =
	//asm volatile("mrc p15, 0, %0, c0, c0, 1" : "=r" (ctr))
	COP_READ2(COP_SYSTEM, "0", COP_ID_CACHE_CONTROL_ARMv7_CLIDR, ctr);
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache2: start_va = 0x%x, end_va = 0x%x\n", start_va, end_va);
	uint32_t cache_line_size_pow2 = (ctr >> 16) & 0xF;	//ctr[3:0] = CTR.DminLine = CTR[19:16] = Log₂(Number of 4-byte words in smallest cache).
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache3: cache_line_size_pow2 = 0x%x\n", cache_line_size_pow2);
	uint32_t cache_line_size_byte = 4 << cache_line_size_pow2;
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache4: cache_line_size_byte = 0x%x\n", cache_line_size_byte);

	uint32_t cache_line_mask = cache_line_size_byte - 1;
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache5: cache_line_mask = 0x%x\n", cache_line_mask);
	uint32_t current_va;
	if (start_va & cache_line_mask) {						//Start address not cache line aligned.
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache6: start_va & cache_line_mask = 0x%x\n", start_va & cache_line_mask);
		current_va = start_va & ~cache_line_mask;			//Cache aligns start_va.
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache7: current_va = 0x%x\n", current_va);
		COP_WRITE(COP_SYSTEM, COP_DCACHE_CLEAN_INVALIDATE_MVA, current_va); //DCCIMVAC, Clean and invalidate data* cache line by MVA to PoC[page 1471].
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache8: Cleaned and invalidated current_va = 0x%x\n", current_va);
		current_va += cache_line_size_byte;
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache9: Update current_va = 0x%x\n", current_va);
	} else {												//Start address cache line aligned.
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache10: Updates current_va\n");
		current_va = start_va;
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache11: Updated current_va = 0x%x\n", current_va);
	}

	if (end_va & cache_line_mask) {							//End address not cache line aligned.
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache12: end_va & cache_line_mask = 0x%x\n", end_va & cache_line_mask);
		uint32_t cache_aligned_end_va = end_va & ~cache_line_mask;		//Cache aligns end_va.
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache13: cache_aligned_end_va = 0x%x\n", cache_aligned_end_va);
		COP_WRITE(COP_SYSTEM, COP_DCACHE_CLEAN_INVALIDATE_MVA, cache_aligned_end_va); //DCCIMVAC, Clean and invalidate data* cache line by MVA to PoC[page 1471].
//printf("Hypervisor hypercall_clean_ends_invalidate_dma_dcache14: Cleaned anv invalidated cache_aligned_end_va = 0x%x\n", cache_aligned_end_va);
	}

	while (current_va < end_va) {
		COP_WRITE(COP_SYSTEM, COP_DCIMVAC, current_va); 	//DCCIMVAC, Clean and invalidate data* cache line by MVA to PoC[page 1471].
		current_va += cache_line_size_byte;
	}

	__asm__ __volatile__ ("dsb st" : : : "memory");
}

void hypercall_cache_op(enum hyp_cache_op op, addr_t va, uint32_t size_or_end)
{
	switch (op) {
	case FLUSH_ALL:
		hypercall_flush_all();
		return;
	case FLUSH_D_CACHE_AREA:
		hypercall_dcache_flush_area(va, size_or_end);
		return;
	case CLEAN_D_CACHE_AREA:
		hypercall_dcache_clean_area(va, size_or_end);
		return;
	case INVAL_D_CACHE_MVA:
		hypercall_dcache_invalidate_mva(va);
		return;
	case FLUSH_I_CACHE_ALL:
		hypercall_icache_invalidate_all();
		return;
	case FLUSH_I_CACHE_MVA:
		hypercall_icache_invalidate_mva(va);
		return;
	case INVAL_ALL_BRANCH:
		hypercall_branch_invalidate_all();
		return;
	case INVAL_TLB_ALL:
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_ALL, 0);
		return;
	case INVAL_TLB_MVA:
		hypercall_tlb_invalidate_mva(va);
		return;
	case INVAL_TLB_ASID:
		hypercall_tlb_invalidate_asid(va);
		return;
	case FLUSH_D_CACHE:
		hypercall_clean_or_invalidate_dcache();
		return;
	case INV_D_CACHE_REGION:
		hypercall_dcache_invalidate_region(va, size_or_end);
		return;
	case CLEAN_D_CACHE_REGION:
		hypercall_dcache_clean_region(va, size_or_end);
		return;
	case COHERENT_RANGE:
		coherent_range((uint32_t) va, size_or_end);
		return;
	case CLEAN_ENDS_INVALIDATE:
		hypercall_clean_ends_invalidate_dma_dcache((uint32_t) va, size_or_end);
		return;
	default:
		printf("Invalid cache operation\n");
	}
}
