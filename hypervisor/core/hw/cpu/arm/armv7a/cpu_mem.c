#include "types.h"
#include "arm_common.h"
#include "cpu_cop.h"
#include "cpu.h"

/*
 * TLB
 * */
//COP_SYSTEM = "p15"
//COP_TLB_INVALIDATE_ALL = "c8, c7, 0"
//COP_TLB_INVALIDATE_ALL_INST = "c8, c5, 0"
//COP_TLB_INVALIDATE_ALL_DATA = "c8, c6, 0"
//@inst: Invalidate entire instruction TLB.
//@data: Invalidate data TLB by ASID = 0.
void mem_mmu_tlb_invalidate_all(BOOL inst, BOOL data)
{
	uint32_t tmp = 0;
	if (inst && data)
		//"Invalidate Inst-TLB and Data-TLB"
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_ALL, tmp);
	else if (inst)
		//ITLBIALL: Invalidate entire instruction TLB, ignores tmp = ASID.
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_ALL_INST, tmp);
	else if (data)
		//DTLBIASID: Invalidate data TLB by ASID match = tmp = 0.
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_ALL_DATA, tmp);
}

void mem_mmu_tlb_invalidate_one(BOOL inst, BOOL data, uint32_t virtual_addr)
{
	uint32_t tmp = virtual_addr;

	if (inst && data)
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA, tmp);
	else if (inst)
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA_INST, tmp);
	else if (data)
		COP_WRITE(COP_SYSTEM, COP_TLB_INVALIDATE_MVA_DATA, tmp);
}

/*
 * CACHES 
 */

/* XXX: this can be simplified alot! /AV */
static inline signed int log_2_n_round_up(uint32_t n)
{
	signed int log2n = -1;
	uint32_t temp = n;

	while (temp) {
		log2n++;
		temp >>= 1;
	}

	if (n & (n - 1))
		return log2n + 1;	/* not power of 2 - round up */
	else
		return log2n;	/* power of 2 */
}

//Cleans data cache (flush changes to other observers) level @level + 1
//(counting from 1 to 7 potentially implemented cache levels).
//@clean_it also invalidates cache (obtain changes from other observers).
static void clean_or_invalidate_dcache_setway(uint32_t level, uint32_t clean_it)
{
	uint32_t csselr, ccsidr;	// cache size selection/id register
	uint32_t num_sets, num_ways, log2_line_len, log2_num_ways;
	uint32_t way_shift;

	//Write level and type you want to extract from cache size selection register
	csselr = level << 1 | ARMV7_CSSELR_IND_DATA_UNIFIED;
	//Writes Cache Size Selection Register (CSSELR) by setting the cache level
	//hierarchy.
	COP_WRITE2(COP_SYSTEM, "2", COP_ID_CPU, csselr);	//COP_ID_CPU = "c0, c0, 0"

	// Get size details from current cache size id register
	//Reads Cache Size ID Register (CCSIDR):
	//31 = WT: Indicates whether the cache level supports write-through.
	//30 = WB: Indicates whether the cache level supports write-back.
	//29 = RA: Indicates whether the cache level supports read-allocation.
	//28 = WAS: Indicates whether the cache level supports write-allocation.
	//27-13 = NumSets: (Number of sets in cache)–1, therefore a value of 0
	//indicates 1 set in the cache. The number of sets does not have to be a
	//power of 2.
	//12-3 = Associativity: (Associativity of cache)–1, therefore a value of 0
	//indicates an associativity of 1. The associativity does not have to be a
	//power of 2.
	//2-0 = LineSize: (Log2(Number of words in cache line))–2.
	COP_READ2(COP_SYSTEM, "1", COP_ID_CPU, ccsidr);

	//CCSIDR_LINE_SIZE_MASK = 0b111
	//log2_line_len = (Log2(Number of words in cache line))–2 + 2 =
	//Log2(Number of words in cache line).
	log2_line_len = (ccsidr & CCSIDR_LINE_SIZE_MASK) + 2;
	/* Converting from words to bytes */
	//log2_line_len = Log2(Number of words in cache line) + 2 =
	//Log2(Number of words in cache line*2^2) =
	//Log2(2^power of two of the number of words in cache line*2^2) =
	//Log2(2^(power of two of the number of words in cache line + 2)) =
	//Log2(2^(power of two of the number of bytes in cache line)) =
	//power of two of the number of bytes in cache line.
	log2_line_len += 2;

	//CCSIDR_ASSOCIATIVITY_MASK = 12-3 are ones
	//CCSIDR_ASSOCIATIVITY_OFFSET = 3
	//num_ways = Associativity of cache = number of available locations in a
	//set = number of available cache lines in a set which an addressed item is
	//mapped to, and way is the number of possible locations/cache lines.
	num_ways = ((ccsidr & CCSIDR_ASSOCIATIVITY_MASK) >> CCSIDR_ASSOCIATIVITY_OFFSET) + 1;
	//CCSIDR_NUM_SETS_MASK = 27-13 are ones
	//CCSIDR_NUM_SETS_OFFSET = 13
	//num_sets = Number of sets in cache.
	num_sets = ((ccsidr & CCSIDR_NUM_SETS_MASK) >> CCSIDR_NUM_SETS_OFFSET) + 1;

	//Binary logarithm of number of cache lines in each set rounded upwards =
	//Number of bits.
	log2_num_ways = log_2_n_round_up(num_ways);

	way_shift = (32 - log2_num_ways);

	int way, set, setway;

	//Set/Way register format:
	//-Level[3:1]: Cache level to operate on - 1.
	//-Set[log2(line byte length) + log2(number of sets) - 1:log2(line byte length)]:
	// Number of the set to operate on.
	//-Way[31:32 - log2(associativity = number of ways)]: The number of the way to operate on.
	// Clears all ways and all sets of data cache.
	for (way = num_ways - 1; way >= 0; way--) {
		for (set = num_sets - 1; set >= 0; set--) {
			setway = (level << 1) | (set << log2_line_len) | (way << way_shift);

			if (clean_it)
				//COP_DCACHE_CLEAN_INVALIDATE_SW = "c7, c14, 2" =
				//"DCCISW, Clean and invalidate data* cache line by set/way"
				COP_WRITE(COP_SYSTEM, COP_DCACHE_CLEAN_INVALIDATE_SW, setway);
			else
				//COP_DCACHE_INVALIDATE_SW = "c7, c10, 2" =
				//"DCCSW, Clean data* cache line by set/way"
				COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_SW, setway);
		}
	}

	/* Data synchronization barrier operation
	 *  to make sure the operation is complete 
	 */
	//"Ensure visibility of the data cleaned from the cache"
	//A DSB completes when:
	//-All explicit memory accesses are complete.
	//-All cache and branch predictor maintenance operations are complete.
	//-All TLB maintenance operations issued are complete.
	dsb();
}

// Viktor
//COP_SYSTEM = "p15"
//COP_ID_CACHE_CONTROL_ARMv7_CLIDR = "c0, c0, 1"
//Invalidates (read observations), and if @clean_it is true flushes (make others
//observe) all data cache levels.
static void clean_or_invalidate_dcache(BOOL clean_it)
{
	uint32_t level, cache_type, level_start_bit = 0;
	uint32_t clidr;

	/* Get cache level ID register */
	//clidr = CLIDR
	COP_READ2(COP_SYSTEM, "1", COP_ID_CACHE_CONTROL_ARMv7_CLIDR, clidr);

//	for (level = 0; level < 8; level++) {	//Ctype goes only between 1 and 7.
	for (level = 0; level < 7; level++) {
		//Obtains Ctype1 through Ctype7 and LoUIS
		//Ctype[i]:
		//-000: No cache
		//-001: Instruction cache only
		//-010: Data cache only
		//-011: Separate instruction and data caches
		//-100: Unified cache
		//
//Bug with level going to <= 7 < 8.
//		//LoUIS =
//		//Level of Unification Inner Shareable for the cache hierarchy =
//		//Read-as-Zero for non Multiprocessor extensions.
		cache_type = (clidr >> level_start_bit) & 0x7;

		if ((cache_type == ARMV7_CLIDR_CTYPE_DATA_ONLY) ||			//2
		    (cache_type == ARMV7_CLIDR_CTYPE_INSTRUCTION_DATA) ||	//3
		    (cache_type == ARMV7_CLIDR_CTYPE_UNIFIED)) {			//4
			//Cleans (flush changes to other observers) all sets and ways (of
			//all cache levels since this is a loop over all cache levels.
			clean_or_invalidate_dcache_setway(level, clean_it);
		}

		level_start_bit += 3;
	}
}

//Flushes (cleans and invalidates) all data caches.
//Handles LoUU, LoC, and LoUIS since clean_or_invalidate_dcache iterates over
//all possible seven levels.
void mem_flush_dcache(void) {
	clean_or_invalidate_dcache(TRUE);
}

//Enables/disables instruction and data caches.
void mem_cache_set_enable(BOOL enable)
{
	uint32_t tmp;

	//COP_SYSTEM_CONTROL = "c1, c0, 0" = SCTLR
	COP_READ(COP_SYSTEM, COP_SYSTEM_CONTROL, tmp);
	if (enable)
		//COP_SYSTEM_CONTROL_ICACHE_ENABLE = 0x0000_1000 = I flag =
		//enabling/disabling instruction caches.
		//COP_SYSTEM_CONTROL_DCACHE_ENABLE = 0x0000_0004 = C flag =
		//enabling/disabling data and unified caches.
		tmp |= (COP_SYSTEM_CONTROL_ICACHE_ENABLE | COP_SYSTEM_CONTROL_DCACHE_ENABLE);
	else
		tmp &= ~(COP_SYSTEM_CONTROL_ICACHE_ENABLE | COP_SYSTEM_CONTROL_DCACHE_ENABLE);
	//Writes SCTLR.
	COP_WRITE(COP_SYSTEM, COP_SYSTEM_CONTROL, tmp);
}

//@inst_inv: Invalidates instruction cache.
//@data_inv: Invalidates (read observations) all data cache levels.
//@data_writeback: Cleans/Flushes (make others observe) all data cache levels.
void mem_cache_invalidate(BOOL inst_inv, BOOL data_inv, BOOL data_writeback)
{
	uint32_t tmp = 1;
	/* first, handle the data cache */
	if (data_inv) {
		//Invalidates (read observations), and if @data_writeback is true
		//flushes (make others observe) all data cache levels.
		clean_or_invalidate_dcache(data_writeback);
	}

	/* now, the instruction cache */
	if (inst_inv) {
		//COP_ICACHE_INVALIDATE_ALL = "c7, c5, 0"
		//Invalidates instruction cache, tmp is ignored.
		COP_WRITE(COP_SYSTEM, COP_ICACHE_INVALIDATE_ALL, tmp);
	}
}

void mem_cache_dcache_area(addr_t va, uint32_t size, uint32_t op)
{
	uint32_t ctr;
	uint32_t cache_size;

	uint32_t end, next;
	//COP_SYSTEM = p15
	//COP_ID_CACHE_CONTROL_ARMv7_CLIDR = "c0, c0, 1"
	//COP_READ2(cop, op1, func, reg) =
	//asm volatile("mrc " cop "," op1 ", %0, " func : "=r" (reg))
	//COP_READ2(COP_SYSTEM, "0", COP_ID_CACHE_CONTROL_ARMv7_CLIDR, ctr) =
	//asm volatile("mrc p15, 0, %0, c0, c0, 1" : "=r" (ctr))
	COP_READ2(COP_SYSTEM, "0", COP_ID_CACHE_CONTROL_ARMv7_CLIDR, ctr);

	ctr = (ctr >> 16) & 0xF;	//ctr[3:0] = CTR.DminLine = CTR[19:16] = Log₂(Number of 4-byte words in smallest cache).
	//4 << Log₂(Number of 4-byte words in smalles cache line) =
	//4*2^(Log₂(Number of 4-byte words in smalles cache line)) =
	//4*(Number of 4-byte words in smalles cache line) =
	//Number of bytes in smalles cache line.
	cache_size = (4 << ctr);

	next = va;
	end = va + size;
	do {
		if (op == FLUSH)
			//DCCIMVAC, Clean and invalidate data* cache line by MVA to PoC.
			//This means that the written address is cleaned and invalidated.
			COP_WRITE(COP_SYSTEM, COP_DCACHE_CLEAN_INVALIDATE_MVA, next);
		else if (op == CLEAN)
			//DCCMVAC, Data Cache Clean by MVA to PoC, VMSA.
			COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, next);

		next += cache_size;
	} while (next < end);

	dsb();
}

/////////
/*
 *@start: Start virtual address.
 *
 *@end: End virtual address (exclusive).
 *
 *Function: For caches containing data:
 *1.Cleans and invalidates the cache line containing the start address if
 *it is not cache line size aligned. The cleaning is done since the first
 *cache line may contain other data not beloning to the DMA region if it
 *is not cache line size aligned.
 *2.Cleans and invalidates the cache line containing the end address if it
 *is not cache line size aligned. The cleaning is done since the last
 *cache line may contain other data not beloning to the DMA region if it
 *is not cache line size aligned.
 *3.Invalidates all cache lines whose cache line aligned addresses are
 *greater than or equal to the cache line size aligned address
 *corresponding to the start address, and less than the cache line size
 *aligned address corresponding to the end address. This means that the
 *end address is exclusive.
 */
void inv_dcache_region(addr_t start, addr_t end)
{
	uint32_t ctr, min_data_cache_line_size, min_data_cache_line_mask;

	//ctr := CTR, Cache Type Register.
	COP_READ(COP_SYSTEM, COP_ID_CACHE_CONTROL_ARMv7_CLIDR, ctr);

	//ctr := ctr >> 16. This is the bit offset of the DminLine field of CTR.
	ctr >>= 16;

	//ctr := CTR.DminLine;
	//Log2 of the number of words in the smallest cache line of all the data
	//caches and unified caches that are controlled by the processor. Hence the
	//cache line size is a power of two. Minimum cache line size is needed to
	//prevent skipping a cache line in the loop.
	ctr &= 0xF;

	//Cache line size in bytes: 2^ctr * 4 =
	//(1 << ctr) * 4 = (1 << ctr) << 2 = 1 << (ctr + 2) =
	//1 << (2 + ctr) = (1 << 2) << ctr = 4 << ctr
	min_data_cache_line_size = 4 << ctr;

	//Cache line size is a power of two. Gives ones below the bit that is set
	//to denote the size. Hence a sort of a mask is stored in r3 that
	//identifies the byte addresses of a cache line.
	min_data_cache_line_mask = min_data_cache_line_size - 1;

	//If the start address is not cache line size aligned, then it is masked to
	//be cache line size aligned, and the cache line containing the word at
	//address start might contain data not pertaining to the invalidation
	//region, and hence that cache line is cleaned and then invalidated.
	if (start & min_data_cache_line_mask) {
		//Makes the start address cache line size aligned.
		start = start & ~min_data_cache_line_mask;

		//DCCIMVAC, Clean and invalidate data (or unified) cache line by MVA to
		//PoC. Invalidates cache line containing the start address.
		COP_WRITE(COP_SYSTEM, COP_DCACHE_CLEAN_INVALIDATE_MVA, start);
	}
	//If the end address is not cache line size aligned, then it is masked to
	//be cache line size aligned, and the cache line containing the word at
	//address end might contain data not pertaining to the invalidation
	//region, and hence that cache line is cleaned and then invalidated.
	if (end & min_data_cache_line_mask) {
		//Makes the end address cache line size aligned.
		end = end & ~min_data_cache_line_mask;

		//DCCIMVAC, Clean and invalidate data (or unified) cache line by MVA to
		//PoC. Invalidates cache line containing the start address.
		COP_WRITE(COP_SYSTEM, COP_DCACHE_CLEAN_INVALIDATE_MVA, end);
	}
	//Invalidates data cache lines containing words at addresses in the
	//interval [start, end) (for values in start and end at this execution
	//point).
	do {
		//DCIMVAC, Invalidate data (or unified) cache line by MVA to PoC.
		//Invalidates the cache line holding the word at address start.
		//Executes: MCR p15, 0, start, c7, c6, 1;
		COP_WRITE(COP_SYSTEM, COP_DCIMVAC, start);

		//Increments the cache line size aligned address in start with the
		//value of the minimum cache line size.
		start += min_data_cache_line_size;
	} while (start < end);

	//Data Synchronization Barrier acts as a special kind of memory barrier. No
	//instruction in program order after this instruction executes until this
	//instruction completes. This instruction completes when:
	//-All explicit memory accesses before this instruction complete.
	//-All Cache, Branch predictor and TLB maintenance operations before this
	// instruction complete.
	dsb();
}

////////

////////
/*
 *@start: Start virtual address.
 *
 *@end: End virtual address (exclusive).
 *
 *Function: Cleans cache lines containing data starting at the address @start
 *and ending at @end. @end is exclusive but is cleaned if it is not the first
 *word of a cache line.
 */
void clean_dcache_region(addr_t start, addr_t end)
{
	uint32_t ctr, min_data_cache_line_size, min_data_cache_line_mask;

	//ctr := CTR, Cache Type Register.
	COP_READ(COP_SYSTEM, COP_ID_CACHE_CONTROL_ARMv7_CLIDR, ctr);

	//ctr := ctr >> 16. This is the bit offset of the DminLine field of CTR.
	ctr >>= 16;

	//ctr := CTR.DminLine;
	//Log2 of the number of words in the smallest cache line of all the data
	//caches and unified caches that are controlled by the processor. Hence the
	//cache line size is a power of two. Minimum cache line size is needed to
	//prevent skipping a cache line in the loop.
	ctr &= 0xF;

	//Cache line size in bytes: 2^ctr * 4 =
	//(1 << ctr) * 4 = (1 << ctr) << 2 = 1 << (ctr + 2) =
	//1 << (2 + ctr) = (1 << 2) << ctr = 4 << ctr
	min_data_cache_line_size = 4 << ctr;

	//Cache line size is a power of two. Gives ones below the bit that is set
	//to denote the size. Hence a sort of a mask is stored in r3 that
	//identifies the byte addresses of a cache line.
	min_data_cache_line_mask = min_data_cache_line_size - 1;

	//Makes the start address cache line size aligned.
	start = start & ~min_data_cache_line_mask;

	//Cleans data cache lines containing words at addresses in the
	//interval [start, end) (for values in start and end at this execution
	//point).
	do {
		//DCCMVAC, Clean data (or unified) cache line by MVA to PoC. Can be
		//executed only by software executing at PL1 or higher. Cleans the
		//cache line containing the data word at address start.
		//Executes: MCR p15, 0, start, c7, c10, 1;
		COP_WRITE(COP_SYSTEM, COP_DCACHE_INVALIDATE_MVA, start);

		//Increments the cache line size aligned address in start with the
		//value of the minimum cache line size.
		start += min_data_cache_line_size;
	} while (start < end);

	//Data Synchronization Barrier acts as a special kind of memory barrier. No
	//instruction in program order after this instruction executes until this
	//instruction completes. This instruction completes when:
	//-All explicit memory accesses before this instruction complete.
	//-All Cache, Branch predictor and TLB maintenance operations before this
	// instruction complete.
	dsb();
}



#define COP_CLEAN_DATA_OR_UNIFIED_CACHE_LINE_BY_MVA_POU	"c7, c11, 1"
#define COP_INVALIDATE_INSTRUCTION_CACHE_BY_MVA_POU	"c7, c5, 1"

void coherent_range(uint32_t start_va, uint32_t end_va) {
	uint32_t ctr;
	COP_READ(COP_SYSTEM, COP_ID_CACHE_CONTROL_ARMv7_CLIDR, ctr);	//ctr = CTR
	uint32_t dminline = (ctr >> 16) & 0xF;			//dminline = CTR.DminLine = "Log2 of the number of words
													// in the smallest cache line of all the data caches
													// and unified caches that are controlled by the processor." =
													//Log₂ (number of 4 byte words in cache line)
	uint32_t cline_words = 0x1 << dminline;			//2^0 << x = 2^0 * 2^x = 2^(0 + x) = 2^x.
													//x = Log₂(number of 4 byte words in cache line)
													//cline_words = 2^(Log₂(number of 4 byte words in cache line)) =
													//number of 4 byte words in cache line
	uint32_t cline_bytes = cline_words*4;			//number of bytes in cache line.

	uint32_t va = start_va & ~(cline_bytes - 1);	//cline_bytes assumed to be a power of 2, and clears
													//the LSBs of start_va to start on a multiple of that
													//number of bytes of the cache line.

	do {
		COP_WRITE(COP_SYSTEM, COP_CLEAN_DATA_OR_UNIFIED_CACHE_LINE_BY_MVA_POU, va);	//Clean D line to PoU.
		va += cline_bytes;
	} while (va < end_va);
	dsb();

	uint32_t iminline = ctr & 0xF;					//iminline = CTR.IminLine = "Log2 of the number of words in the
													// smallest cache line of all the instruction caches that are
													// controlled by the processor."
	cline_words = 0x1 << iminline;					//number of 4 byte words in cache line.
	cline_bytes = cline_words*4;					//number of bytes in cache line.	

	va = start_va & ~(cline_bytes - 1);				//cline_bytes assumed to be a power of 2, and clears
													//the LSBs of start_va to start on a multiple of that
													//number of bytes of the cache line.

	do {
		COP_WRITE(COP_SYSTEM, COP_INVALIDATE_INSTRUCTION_CACHE_BY_MVA_POU, va);	//Invalidate instruction line to PoU.
		va += cline_bytes;
	} while (va < end_va);

	COP_WRITE(COP_SYSTEM, COP_BRANCH_PRED_INVAL_ALL, 0);	//Invalidates all branch predictors.
	dsb();
	isb();
}

//////////////
