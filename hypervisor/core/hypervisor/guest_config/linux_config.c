#include "hyper_config_base.h"
#include "hyper_config.h"

// #define GUEST_LOCATION 0xF1000000
#define TRUSTED_LOCATION 0xf0500000
#define BUFFER_LENGTH 38960
// #define BUFFER_LENGTH 65000
// #define TRUSTED_LOCATION 0xF0A00000
#define CAKEML_INPUT_BUFFER_SZ	BUFFER_LENGTH
#define CAKEML_OUTPUT_BUFFER_SZ	BUFFER_LENGTH
#define CAKEML_BUFFER_SIZE (CAKEML_INPUT_BUFFER_SZ + CAKEML_OUTPUT_BUFFER_SZ)
#define TRUSTED_ENTRY (TRUSTED_LOCATION)
#define TRUSTED_RPC   ((TRUSTED_LOCATION) + 4 + CAKEML_BUFFER_SIZE)
#define TRUSTED_SP    ((TRUSTED_LOCATION) + 0x00100000 - 4)	/* ??? */

/*
 * Bitmask constants for specifying guest mode
 * contexts that can be get/set.
 */
#define HC_GM_TRUSTED_MASK   (1 << HC_GM_TRUSTED)
#define HC_GM_KERNEL_MASK    (1 << HC_GM_KERNEL)
#define HC_GM_TASK_MASK      (1 << HC_GM_TASK)

/*
 * Guest mode access to certain domains
 * ********************************************************/

#define HC_DOMAC_ALL				\
  ((1 << (2 * HC_DOM_DEFAULT)) |		\
   (1 << (2 * HC_DOM_TASK)) |			\
   (1 << (2 * HC_DOM_KERNEL)) |			\
   (1 << (2 * HC_DOM_TRUSTED)))

//Kernel has no access to trusted guest.
//1 << 2*0 = 1
//DACR[1:0] = 1 = Client
//1 << 2*1 = 0x4
//DACR[3:2] = 1 = Client
//1 << 2*2 = 0x10
//DACR[5:4] = 1 = Client
//DACR[7:6] = 0 = No Access.
#define HC_DOMAC_KERNEL				\
  ((1 << (2 * HC_DOM_DEFAULT)) |		\
   (1 << (2 * HC_DOM_KERNEL)) |			\
   (1 << (2 * HC_DOM_TASK)))

//Trusted has no access to Linux.
//1 << 2*0 = 1
//1 << 2*3 = 1 << 6 = 0x10 << 2 = 0x40
//DACR[1:0] = 1 = Client
//DACR[3:2] = 0 = No Access
//DACR[5:4] = 0 = No Access
//DACR[7:6] = 1 = Client
#define HC_DOMAC_TRUSTED			\
  ((1 << (2 * HC_DOM_DEFAULT)) |		\
   (1 << (2 * HC_DOM_TRUSTED)))

#define HC_DOMAC_TASK				\
  ((1 << (2 * HC_DOM_DEFAULT)) |		\
   (1 << (2 * HC_DOM_TASK)))

/************************************************************/

/*
 * Configuration for guest modes
 */

static const hc_guest_mode
gm_trusted = {
	.name = "trusted",
	.domain_ac = HC_DOMAC_TRUSTED,
},
gm_kernel = {
	.name = "kernel",
	.domain_ac = HC_DOMAC_KERNEL,},
gm_task = {
	.name = "application",
	.domain_ac = HC_DOMAC_TASK,
};

/*RPC handler*/
static const hc_rpc_handler rpc_handler_trusted = {
	.name = "trusted_rpc_handler",
	.mode = HC_GM_TRUSTED,
	.entry_point = TRUSTED_RPC,
	.sp = TRUSTED_SP
};

/*
 * Guest configuration structure
 */

hc_config linux_config = {
	.guest_entry_offset = 0x10000,
	//Guest can enter trusted (), kernel (OS) and task (application) modes.
	.guest_modes = {&gm_trusted, &gm_kernel, &gm_task},
	.rpc_handlers = &rpc_handler_trusted,
/*
0xC000_0000 + 0x3000_0000 - 0x0800_0000 =
0xF000_0000 - 0x0800_0000 =
0xE000_0000 + 0x0800_0000 + 0x0800_0000 - 0x0800_0000 =
0xE000_0000 + 0x0800_0000 =
0xE800_0000 =

3GB - 128MB

0xE800_0000-0xF000_0000 for DMMU

See modification of arch/arm/include/asm/pgtable.h:VMALLOC_END
*/
	//Start virtual address used by hypervisor to access Linux memory.
	.reserved_va_for_pt_access_start = 0xE8000000,
	// Offset respect the initial pa of the guest
	.pa_initial_l1_offset = 0x00004000,	// Offset to master page table in Linux
	/*L2 offset is the end of the guest physical memory, 1MB */
	//Used by:
	//-dmmu_clear_linux_mappings
	//-hypercall_linux_init_end, which is never invoked.
	//-linux_pt_get_empty_l2, which is invoked by init_linux_dmmu
	//-linux_init_dmmu
	//-guests_init
	//hyp_dmmu.c
	.pa_initial_l2_offset = 0x0,	//Updated by guests_init to psize = 0x0700_0000 to give the location where the L2 page tables are stored.
	//.always_cached_offset = 0x0,
	//.always_cached_size = (0x6A00000 - 0x0)
	//Executable code is between 0xC000_0000 and 0xC200_0000 initially. Used during guests_init().
	.initial_kernel_ex_va_top = 0xC2000000,
	.runtime_kernel_ex_va_top = 0xC2000000,
	//Executable code between 0xC000_0000 and 0xC07C7FFFF during boot, used by dmmu_clear_linux_mappings.
	.init_kernel_ex_va_top = 0xC2000000,
};
