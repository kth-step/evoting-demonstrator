#include <types.h>

#include "hypercalls.h"
#include "test_x_ref.h"

extern uint32_t va_base;
extern addr_t pstart;

enum dmmu_command {
	CMD_MAP_L1_SECTION, CMD_UNMAP_L1_PT_ENTRY, CMD_CREATE_L2_PT,
	    CMD_MAP_L1_PT, CMD_MAP_L2_ENTRY, CMD_UNMAP_L2_ENTRY, CMD_FREE_L2,
	    CMD_CREATE_L1_PT, CMD_SWITCH_ACTIVE_L1, CMD_FREE_L1
};

extern uint32_t syscall_dmmu(uint32_t r0, uint32_t r1, uint32_t r2);
#define ISSUE_DMMU_HYPERCALL(type, p0, p1, p2) \
		syscall_dmmu(type | (p2 << 4), p0, p1);

#define ISSUE_DMMU_HYPERCALL_(type, p0, p1, p2, p3) \
		syscall_dmmu((type | (p2 & 0xFFFFFFF0)), p0, ((p1 << 20) | p3));

#define ISSUE_DMMU_QUERY_HYPERCALL(p0) \
		syscall_dmmu_query(p0);


void test_xref_5MB_allocated()
{
	int i;
	for (i=1; i<5; i++) {
		// Slik the MB2 since there is already the initial L2 page table
		if (i != 2) {
			uint32_t va = (va_base + i * 0x100000);
			*((uint32_t*)va) = i;
			expect(i-1, "Writing from the next MB", 0, 0);
			expect(i-1, "Reading from the next MB", i, *((uint32_t*)va));
		}
	}	
}

void test_xref_create_empty_l2() {
	// we use the base_address + 1MB
	uint32_t va = (va_base + 1 * 0x100000);
	uint32_t pa;
	uint32_t i;
	uint32_t res;
	for (i=0; i<1024; i++) {
		uint32_t va1 = (va + i * 4);
		*((uint32_t*)va1) = 0;
	}

	//Querying the data structure for the memory at the start of the physical memory
	res = ISSUE_DMMU_QUERY_HYPERCALL(pstart);
	dmmu_entry_t bft_entry = (dmmu_entry_t) res;
	expect(0, "Reference counter", 1, bft_entry.refcnt);
	expect(0, "Executable reference counter", 1, bft_entry.x_refcnt);
	expect(0, "Type", 0, bft_entry.type);

	//Trying to create a L2 pt in a referenced region
	pa = pstart + 1 * 0x100000;
	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L2_PT, pa, 0, 0);
	expect(1, "Creating the L2 in a referenced region", 21, res);

	//Querying the data structure for the memory region above, reference counter should be 1
	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(2, "Reference counter", 1, bft_entry.refcnt);
	expect(2, "Executable reference counter", 1, bft_entry.x_refcnt);
	expect(2, "Type", 0, bft_entry.type);


	//Unmapping 0xC0010000
	res = ISSUE_DMMU_HYPERCALL(CMD_UNMAP_L1_PT_ENTRY, va, 0, 0);
	expect(3, "Unmap 0xC0010000 that was mapping the L2", 0, res);

	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(4, "Reference counter", 0, bft_entry.refcnt);
	expect(4, "Executable reference counter", 0, bft_entry.x_refcnt);
	expect(4, "Type", 0, bft_entry.type);
	//***************************************************************
	
	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_PT, va, pa, 0);
	expect(5, "Mapping 0xC01... using the L2 just created but still typed D", 12, res);

	//Creating a L2 page table at address pa
	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L2_PT, pa, 0, 0);
	expect(6, "Creating the L2 in a non-referenced region", 0, res);

	//Mapping 0xC0010000 to the L2 page table just creaed
	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_PT, va, pa, 0);
	expect(7, "Mapping 0xC01... using the L2 just created", 0, res);
	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(8, "Reference counter", 1, bft_entry.refcnt);
	expect(8, "Executable reference counter", 0, bft_entry.x_refcnt);
	expect(8, "Type", 2, bft_entry.type);
	//end of L2 page table creation.
	//****************************************************

	//uint32_t  va2 = (va_base + 1 * 0x110000);
	//res = ISSUE_DMMU_HYPERCALL(CMD_UNMAP_L1_PT_ENTRY, va2, 0, 0);
	//expect(9, "Unmapping the memory area where the created L2 is going to be mapped to", 0,
	//       res);
	
	uint32_t pga = pstart + 1 * 0x110000;
	uint32_t pa2 = pa + 1 * 0x100000;
	res = ISSUE_DMMU_HYPERCALL_(CMD_MAP_L2_ENTRY, pa2, 0, pga, 0);
	expect(10, "Mapping a valid physical address into one of a non valid L2",
	       12, res);
	
	res = ISSUE_DMMU_HYPERCALL_(CMD_MAP_L2_ENTRY, pa, 0, pga, 0x32 | 0x8);
	expect(11, "Mapping a valid physical address into one of a valid L2",
	       0, res);
	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	//The result of the reference counter here is 0 because we unmapped the same region above at test id 9
	expect(12, "Reference counter", 1, bft_entry.refcnt);
	expect(12, "Executable reference counter", 0, bft_entry.x_refcnt);
	expect(12, "Type", 2, bft_entry.type);

	res = ISSUE_DMMU_QUERY_HYPERCALL(pga);
	bft_entry = (dmmu_entry_t) res;
	expect(13, "Reference counter", 1, bft_entry.refcnt);
	expect(13, "Executable reference counter", 1, bft_entry.x_refcnt);
	expect(13, "Type", 0, bft_entry.type);
	//***************************************************************

}

void test_xref_create_l1_pt() {
	uint32_t va = (va_base + 1 * 0x100000);
	uint32_t pa;
	uint32_t i;
	uint32_t res;
	dmmu_entry_t bft_entry;

	pa = 0x0;
	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L1_PT, pa, 0, 0);
	expect(0, "Creating L1 in PA outside the allowed guest memory",
	      3, res);

	pa = pstart + 1 * 0x100000;
	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L1_PT, pa, 0, 0);
	expect(0, "Creating an L1 on referenced part of the memory", 
	       21, res);

	res = ISSUE_DMMU_HYPERCALL(CMD_UNMAP_L1_PT_ENTRY, va, 0, 0);
	expect(0, "Unmap 0xC0010000 that was mapping the L1", 0, res);
	
	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L1_PT, pa, 0, 0);
	expect(0, "Creating an L1 on a non referenced part of the memory", 
	       0, res);

	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(0, "Reference counter", 0, bft_entry.refcnt);
	expect(0, "Executable reference counter", 0, bft_entry.x_refcnt);
	expect(0, "Type", 1, bft_entry.type);

	
	//Create another L1 page table
	uint32_t pa2 = pstart + 1 * 0x300000;
	uint32_t va2 = va_base + 1 * 0x300000;
	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L1_PT, pa2, 0, 0);
	expect(0, "Creating an L1 on a non referenced part of the memory", 
	       21, res);

	res = ISSUE_DMMU_HYPERCALL(CMD_UNMAP_L1_PT_ENTRY, va2, 0, 0);
	expect(0, "Unmap 0xC0010000 that was mapping the L1", 0, res);

	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L1_PT, pa2, 0, 0);
	expect(0, "Creating an L1 on a non referenced part of the memory", 
	       0, res);

	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(0, "Reference counter", 0, bft_entry.refcnt);
	expect(0, "Executable reference counter", 0, bft_entry.x_refcnt);
	expect(0, "Type", 1, bft_entry.type);
}

void test_xref_l1_pt_map() {
	uint32_t va = (va_base + 1 * 0x100000);
	uint32_t pa;
	uint32_t i;
	uint32_t res;

	res = ISSUE_DMMU_HYPERCALL(CMD_UNMAP_L1_PT_ENTRY, va, 0, 0);
	expect(0, "Unmap 0xC0100000 that was mapping the L1", 0, res);
	
	//Create an L1
	pa = pstart + 1 * 0x100000;
	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L1_PT, pa, 0, 0);
	expect(0, "Creating an L1 on a non referenced part of the memory", 
	       0, res);

	//Create an L2 to map
	pa = pstart + 1 * 0x110000;
	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L2_PT, pa, 0, 0);
	expect(0, "Successful creation of a new L2", 0, res);

	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_PT, va, pa, 0);
	expect(0, "Mapping again the vm to the L1 page just created", 
	       0, res);

	//Creating another L2 to map
	//This test should fail. It's created in a region which is already page table.
	pa = pstart + 1 * 0x200000;
	res = ISSUE_DMMU_HYPERCALL(CMD_CREATE_L2_PT, pa, 0, 0);
	expect(0, "Unsuccessful creation of a new L2 in a region already page table", 
	       10, res);

	//Mapping the L1 to a region which is not L2 page table
	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_PT, va, pa, 0);
	expect(0, "Mapping again the vm to the L1 page just created", 
	       12, res);

	//TODO
	//Unmapping a region of memory
	res = ISSUE_DMMU_HYPERCALL(CMD_UNMAP_L1_PT_ENTRY, va + 0x200000, 0, 0);
	expect(0, "Unmap 0xC0300000 that was mapping the L1", 0, res);

	//Mapping a region which is not L1 to an L2
	pa = pstart + 1 * 0x110000;
	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_PT, va + 0x200000, pa, 0);
	expect(0, "Mapping a region which is not L1 to an L2", 
	       0, res);

}

void test_x_refcnt()
{
	printf("HELLO\n");
}

void test_xref_unmap_l1_entry() {
	uint32_t va;
	uint32_t pa;
	uint32_t i;
	uint32_t res;
	dmmu_entry_t bft_entry;

	//Fail, unmapping a reserved va
	va = 0x0;
	res = ISSUE_DMMU_HYPERCALL(CMD_UNMAP_L1_PT_ENTRY, va, 0, 0);
	expect(0, "Unmap a reserved va", 1, res);

	va = (va_base + 0x100000);
	pa = pstart + 1 * 0x100000;

	
	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(0, "Reference counter", 1, bft_entry.refcnt);
	expect(0, "Executable reference counter", 1, bft_entry.x_refcnt);
	expect(0, "Type", 0, bft_entry.type);

	res = ISSUE_DMMU_HYPERCALL(CMD_UNMAP_L1_PT_ENTRY, va, 0, 0);
	expect(1, "Unmapping a valid writable page", 0, res);

	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(2, "Reference counter", 0, bft_entry.refcnt);
	expect(2, "Executable reference counter", 0, bft_entry.x_refcnt);
	expect(2, "Type", 0, bft_entry.type);


	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_SECTION, va, pa, 0xc2e);
	expect(3, "Mapping a valid writable page", 0, res);
	
	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(4, "Reference counter", 1, bft_entry.refcnt);
	expect(4, "Executable reference counter", 1, bft_entry.x_refcnt);
	expect(4, "Type", 0, bft_entry.type);

	uint32_t va2 = va_base + 0x300000;
	res = ISSUE_DMMU_HYPERCALL(CMD_UNMAP_L1_PT_ENTRY, va2, 0, 0);
	expect(1, "Unmapping a valid writable page", 0, res);

	/*
	//Mapping this section to some random physical memory
	uint32_t pa2 = pstart + 0x200000;
	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_SECTION, va2, pa2, 0xc2e);
	expect(30, "Mapping a valid writable page", 0, res);
	*/

	//Mapping this section to the same physical address as the previous section
	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_SECTION, va2, pstart, 0xc2e);
	expect(3, "Mapping a valid writable page", 0, res);

	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(4, "Reference counter", 2, bft_entry.refcnt);
	expect(4, "Executable reference counter", 2, bft_entry.x_refcnt);
	expect(4, "Type", 0, bft_entry.type);
	

	//TODO
	int x = 10;	
	uint32_t add = (uint32_t) (&x);
	printf("Address value is: %x\n", add);
	uint32_t next_add = add + 0x300000;
	printf("Address value is: %x\n", next_add);
	expect(5, "The value is: ", 10, *(int*) next_add);

	*(int*)(va + 0x10000) = 7;
	expect(6, "The value is: ", 7, *(int*) (va2 + 0x10000));

	int (*func)();
	func = &test_x_refcnt;
	//*(int*)va = func;
	(*(void(*)())(func + 0x300000))();

	/*
	//Putting a function pointer in the memory section
	int (*func)();
	func = &test_x_refcnt;
	next_add = func + 0x200000;
	(*(void(*)())next_add)();
	
	
	res = ISSUE_DMMU_QUERY_HYPERCALL(pa);
	bft_entry = (dmmu_entry_t) res;
	expect(4, "Reference counter", 2, bft_entry.refcnt);
	expect(4, "Executable reference counter", 2, bft_entry.x_refcnt);
	expect(4, "Type", 0, bft_entry.type);
	*/
}

void test_xref_map_l1_section()
{
	uint32_t va;
	uint32_t pa;
	uint32_t i;
	uint32_t res;
	dmmu_entry_t bft_entry;

	va = 0x0;
	pa = 0x0;
	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_SECTION, va, pa, 0);
	expect(0, "Map of reserved virtual address", 1, res);

	va = va_base + 1 * 0x100000;
	pa = pstart + 1 * 0x100000;

	res = ISSUE_DMMU_HYPERCALL(CMD_MAP_L1_SECTION, va, pa, 0);
	expect(0, "Map an already mapped entry",
	       4, res);
	
}

void test_xref_query() {
	uint32_t res;
	res = ISSUE_DMMU_QUERY_HYPERCALL(pstart);

	dmmu_entry_t bft_entry = (dmmu_entry_t) res;
	
	printf("Refcnt 0x%x\n", res);
	expect(0, "Reference counter", 1, bft_entry.refcnt);
	expect(0, "Executable reference counter", 1, bft_entry.x_refcnt);
	expect(0, "Type", 0, bft_entry.type);

	res = ISSUE_DMMU_QUERY_HYPERCALL(pstart + 0x200000);

	bft_entry = (dmmu_entry_t) res;
	
	printf("Refcnt 0x%x\n", res);
	expect(0, "Reference counter", 0, bft_entry.refcnt);
	expect(0, "Executable reference counter", 0, bft_entry.x_refcnt);
	expect(0, "Type", 1, bft_entry.type);
}

void test_xref_1()
{
	int x = 0+5;
	expect(0, "I add 0 to a number", 5, x);
	expect(1, "I add 0 to a number", 3, x);
	printf("Hello test 1\n");
}

void test_xref_2()
{
	printf("Hello test 2\n");
}

void main_x_ref()
{
#ifdef TEST_XREF_5MB_ALLOCATED
	test_xref_5MB_allocated();
#endif
#ifdef TEST_XREF_CREATE_EMPTY_L2
	test_xref_create_empty_l2();
#endif
#ifdef TEST_XREF_CREATE_L1_PT
	test_xref_create_l1_pt();
#endif
#ifdef TEST_XREF_L1_PT_MAP
	test_xref_l1_pt_map();
#endif
#ifdef TEST_XREF_UNMAP_L1_ENTRY
	test_xref_unmap_l1_entry();
#endif
#ifdef TEST_XREF_MAP_L1_SECTION
	test_xref_map_l1_section();
#endif
#ifdef TEST_XREF_QUERY
	test_xref_query();
#endif
#ifdef TEST_EX_1	
	test_xref_1();
#endif
#ifdef TEST_EX_2
	test_xref_2();
#endif
	printf("TEST COMPLETED\n");
}
