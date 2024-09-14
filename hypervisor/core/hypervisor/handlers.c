#include <hw.h>
#include "hypercalls.h"
#if defined(LINUX) && defined(CPSW)
#include <soc_cpsw.h>
#endif
#include <tptc.h>
#include "dmmu.h"

extern virtual_machine *curr_vm;

#define USE_DMMU

// Disabling aggressive flushing
//#define AGGRESSIVE_FLUSHING_HANDLERS

//Used by END_RPC to know the size of the input buffer of Linux.
char *linux_input_buffer;
uint32_t linux_input_buffer_size;

void clean_and_invalidate_cache()
{
#ifdef AGGRESSIVE_FLUSHING_HANDLERS
	isb();
	mem_mmu_tlb_invalidate_all(TRUE, TRUE);
	CacheDataCleanInvalidateAll();
	dsb();
#endif
}

void swi_handler(uint32_t param0, uint32_t param1, uint32_t param2, uint32_t hypercall_number)
{
//  if ((hypercall_number == HYPERCALL_RESTORE_REGS) || (hypercall_number == HYPERCALL_RESTORE_LINUX_REGS) && (hypercall_number != HYPERCALL_SET_TLS_ID) ){
//      printf("SWI ENTER hypercall_number = %d %x %x %x\n", hypercall_number, param0, param1, param2);
//  }
	/*TODO Added check that controls if it comes from user space, makes it pretty inefficient, remake later */
	/*Testing RPC from user space, remove later */
	if (curr_vm->current_guest_mode == HC_GM_TASK) {
		if (hypercall_number == 1020) {
			//ALLOWED RPC OPERATION
			hypercall_rpc(/*param0*/);
			return;
		} else if (hypercall_number == 1021) {
			hypercall_end_rpc(0);
			return;
		}
	}
	if (curr_vm->current_guest_mode == HC_GM_TASK) {	//Linux application running.
/////////////////////
		if ((curr_vm->current_mode_state->ctx.psr & IRQ_MASK) != 0)
			printf
			    ("ERROR (interrupt delivered when disabled) IRQ_MASK = %x\n",
			     curr_vm->current_mode_state->ctx.psr);
/////////////////////

		//  debug("\tUser process made system call:\t\t\t %x\n",  curr_vm->mode_states[HC_GM_TASK].ctx.reg[7] );
		change_guest_mode(HC_GM_KERNEL);				//Linux now executing in kernel mode.
		/*The current way of saving context by the hypervisor is very inefficient,
		 * can be improved alot with some hacking and shortcuts (for the FUTURE)*/
		curr_vm->current_mode_state->ctx.sp -= (72 + 8);	//FRAME_SIZE (18 registers to be saved) + 2 swi args
		uint32_t *context, *sp, i;

		context = &curr_vm->mode_states[HC_GM_TASK].ctx.reg[0];
		sp = (uint32_t *) curr_vm->mode_states[HC_GM_KERNEL].ctx.sp;

		*sp++ = curr_vm->mode_states[HC_GM_TASK].ctx.reg[4];
		*sp++ = curr_vm->mode_states[HC_GM_TASK].ctx.reg[5];

		i = 17;		//r0-lr

		while (i > 0) {
			*sp++ = *context++;
			i--;
		}

		*sp = curr_vm->mode_states[HC_GM_TASK].ctx.reg[0];	//OLD_R0

		//update CR for alignment fault
		//Enable IRQ
		curr_vm->current_mode_state->ctx.psr &= ~(IRQ_MASK);

		curr_vm->current_mode_state->ctx.lr = curr_vm->exception_vector[V_RET_FAST_SYSCALL];
		//curr_vm->handlers.syscall.ret_fast_syscall;
		//copy task context to kernel context. syscall supports 6 arguments

		/*system call nr in r7 */
		curr_vm->current_mode_state->ctx.reg[7] = curr_vm->mode_states[HC_GM_TASK].ctx.reg[7];

		if (curr_vm->mode_states[HC_GM_TASK].ctx.reg[7] < curr_vm->guest_info.nr_syscalls) {
			/*Regular system call, restore params */
			for (i = 0; i <= 5; i++)
				curr_vm->current_mode_state->ctx.reg[i] = curr_vm->mode_states[HC_GM_TASK].ctx.reg[i];
			/*Set PC to systemcall function */
			curr_vm->current_mode_state->ctx.pc = *((uint32_t *) (curr_vm->exception_vector[V_SWI] + (curr_vm->current_mode_state->ctx.reg[7] << 2)));
		} else {
			//TODO Have not added check that its a valid private arm syscall, done anyways inside arm_syscall
			//if(curr_vm->current_mode_state->ctx.reg[7] >= 0xF0000){ //NR_SYSCALL_BASE
			/*Arm private system call */
			curr_vm->current_mode_state->ctx.reg[0] = curr_vm->mode_states[HC_GM_TASK].ctx.reg[7];
			curr_vm->current_mode_state->ctx.reg[1] = curr_vm->mode_states[HC_GM_KERNEL].ctx.sp + 8;	//Adjust sp with S_OFF, contains regs
			curr_vm->current_mode_state->ctx.pc = curr_vm->exception_vector[V_ARM_SYSCALL];
		}
	} else if (curr_vm->current_guest_mode != HC_GM_TASK) {
		//    printf("\tHypercallnumber: %d (%x, %x) called\n", hypercall_number, param0, param);
		uint32_t res;
		switch (hypercall_number) {
			/* TEMP: DMMU TEST */
		case 666:

			clean_and_invalidate_cache();

			res = dmmu_handler(param0, param1, param2);
			curr_vm->current_mode_state->ctx.reg[0] = res;

			clean_and_invalidate_cache();

			return;
		case HYPERCALL_DBG:
			printf("To here %x\n", param0);
			return;
		case HYPERCALL_GUEST_INIT:
			printf("Hypercall 5: vector_table = 0x%x.\n", param0);
			hypercall_guest_init(param0);
			return;
		case HYPERCALL_INTERRUPT_SET:
			hypercall_interrupt_set(param0, param1);
			return;
		case HYPERCALL_END_INTERRUPT:
			hypercall_end_interrupt(param0);
			return;
		case HYPERCALL_INTERRUPT_CTRL:
			hypercall_interrupt_ctrl(param0, param1);
			return;
		case HYPERCALL_CACHE_OP:
			hypercall_cache_op(param0, param1, param2);
			return;
		case HYPERCALL_SET_TLS_ID:
			hypercall_set_tls(param0);
			return;
		case HYPERCALL_SET_CTX_ID:
			COP_WRITE(COP_SYSTEM, COP_CONTEXT_ID_REGISTER, param0);
			isb();
			return;
			/*Context */
		case HYPERCALL_RESTORE_LINUX_REGS:
			hypercall_restore_linux_regs(param0, param1);
			return;
		case HYPERCALL_RESTORE_REGS:
			hypercall_restore_regs((uint32_t *) param0);
			return;

			/*Page table operations */
		case HYPERCALL_SWITCH_MM:
//			printf("HYPERCALL_SWITCH_MM: pmd = 0x%x, desc = 0x%x, pc = 0x%x.\n", param0, param1, curr_vm->current_mode_state->ctx.pc);
			clean_and_invalidate_cache();
			hypercall_dyn_switch_mm(param0, param1);
			//clean_and_invalidate_cache();
			return;

		case HYPERCALL_NEW_PGD:
//			printf("HYPERCALL_NEW_PGD %x\n", param0);
			clean_and_invalidate_cache();
			hypercall_dyn_new_pgd((uint32_t *) param0);
//if (get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(0x82DE0000))->type == 2) printf("HYPERCALL_NEW_PGD = %d\n", get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(0x82DE0000))->type);
			//clean_and_invalidate_cache();
			return;
		case HYPERCALL_FREE_PGD:
			clean_and_invalidate_cache();
			hypercall_dyn_free_pgd((uint32_t *) param0);
			//clean_and_invalidate_cache();
			return;
		case HYPERCALL_CREATE_SECTION:
			{
				printf("HYPERVISOR hypercall_number = %d %x %x %x NOT IMPLEMENTED!\n", HYPERCALL_CREATE_SECTION, param0, param1, param2);
while (1);
				//printf("SWI ENTER hypercall_number = %d %x %x %x\n", hypercall_number, param0, param1, param2);
				return;
			}

		case HYPERCALL_SET_PMD:
//			printf("HYPERCALL_SET_PMD: pmd = 0x%x, desc = 0x%x, pc = 0x%x.\n", param0, param1, curr_vm->current_mode_state->ctx.pc);

			clean_and_invalidate_cache();

			uint32_t pmd = param0;
			uint32_t desc = param1;
//			merge_with_initial_l2_page_table(pmd, desc);
			hypercall_dyn_set_pmd(param0, param1);
//			printf("HYPERCALL_SET_PMD2 = %x %x!\n", param0, param1);
			//clean_and_invalidate_cache();

			return;

		case HYPERCALL_UPDATE_PMD_SINGLE:
			clean_and_invalidate_cache();
			hypercall_dyn_update_pmd_single(param0, param1, param2);
			return;

		case HYPERCALL_SET_PTE: {
			//param0 = va of l2 pte, param1 = Linux pte, param2 = Hardware pte.
			addr_t * l2_pte_va = (addr_t *) param0;
			uint32_t lpte = param1;
			uint32_t hpte = param2;

//			map_allocated_page_table(param0);

//			printf("HYPERCALL_SET_PTE: l2_pte_va = 0x%x, lpte = 0x%x, hpte = 0x%x, pc = 0x%x.\n", l2_pte_va, lpte, hpte, curr_vm->current_mode_state->ctx.pc);

//			print_ap(hpte);
			hpte = adjust_aps(hpte);
//			print_ap(hpte);
			clean_and_invalidate_cache();
//uint32_t type = get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(0x82DE0000))->type;
			hypercall_dyn_set_pte(l2_pte_va, lpte, hpte);
//if (l2_pte_va == 0xC1DE17FC) print_specific_L2();
//if (type != 2 && get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(0x82DE0000))->type == 2) {
//	printf("HYPERCALL_SET_PTE = %d\n", get_bft_entry_by_block_idx(PA_TO_PH_BLOCK(0x82DE0000))->type);
//	printf("HYPERCALL_SET_PTE2 = VA of L2 PTE = 0x%x, LPTE = 0x%x, HWPTE = 0x%x!\n", l2_pte_va, lpte, hpte);
//	printf("l1desc = 0x%x\n", *((uint32_t *) (0xC0004000 + 0xE9D*4)));
//	while (1);
//}
//			printf("HYPERCALL_SET_PTE2 = VA of L2 PTE = 0x%x, LPTE = 0x%x, HWPTE = 0x%x!\n", l2_pte_va, lpte, hpte);
			//clean_and_invalidate_cache();
			return;
		}

    /****************************/
		 case HYPERCALL_RPC: {
			hypercall_rpc();
			return;
		} case HYPERCALL_END_RPC: {
			uint32_t result = curr_vm->current_mode_state->ctx.reg[0];
//These macros also exist in core/hypervisor/init.c and similar ones in core/hypervisor/guest_config/linux_config.c.
#define BUFFER_LENGTH 38960
#define TRUSTED_LOCATION 0xf0500000
// #define BUFFER_LENGTH 65000
// #define TRUSTED_LOCATION 0xF0A00000
#define CAKEML_INPUT_BUFFER_VA	TRUSTED_LOCATION
#define CAKEML_INPUT_BUFFER_SZ	BUFFER_LENGTH
#define CAKEML_OUTPUT_BUFFER_VA	(TRUSTED_LOCATION + CAKEML_INPUT_BUFFER_SZ)
#define CAKEML_OUTPUT_BUFFER_SZ	BUFFER_LENGTH

			char *cakeml_output_buffer = (char *)CAKEML_OUTPUT_BUFFER_VA;
			int i;
			for (i = 0; i < linux_input_buffer_size && i < CAKEML_OUTPUT_BUFFER_SZ && i < result; i++)
				linux_input_buffer[i] = cakeml_output_buffer[i];

			//Must be after copying of buffers so that the hypervisor has access to the CakeML
			//buffer.
			hypercall_end_rpc(result);

			return;
		}

		case HYPERCALL_LINUX_INIT_END:	//NOT USED!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
			hypercall_linux_init_end();
			return;

		case HYPERCALL_UPDATE_MONITOR: {
			uint32_t number_of_signatures = param0;
			uint32_t *kernel_image = (uint32_t *) param1;
			uint32_t *kernel_image_signature = (uint32_t *) param2;
			printf("HYPERVISOR: HYPERCALL_UPDATE_MONITOR\n");
			printf("HYPERVISOR: number_of_signatures = %d\n", number_of_signatures);
			printf("HYPERVISOR: kernel_image = %x\n", kernel_image);
			printf("HYPERVISOR: kernel_image_signature = %x\n", kernel_image_signature);

			//Successful update of the monitor.
			curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[0] = 0;

			return;
		}
		case HYPERCALL_QUERY_BFT:
			res = dmmu_query_bft(param0);
			curr_vm->current_mode_state->ctx.reg[0] = res;
			return;

		case 1045:
			printf("HYPERVISOR PRINTF: r0 = 0x%x, r1 = 0x%x, r2 = 0x%x\n", curr_vm->current_mode_state->ctx.reg[0], curr_vm->current_mode_state->ctx.reg[1], curr_vm->current_mode_state->ctx.reg[2]);
while (1);
			return;

		case 1046: {		//Read CPU ID
			unsigned int cpuid_reg = (unsigned int) param0;
			unsigned int cpu_id;
			unsigned int *cpuid_out_ptr = (unsigned int *) param1;
			switch (cpuid_reg) {
			case 0: //CPUID_ID
				asm volatile ("mrc	p15, 0, %0, c0, c0, 0" : "=r" (cpu_id) : : "cc"); break;
			case 1:	//CPUID_CACHETYPE
				asm volatile ("mrc	p15, 0, %0, c0, c0, 1" : "=r" (cpu_id) : : "cc"); break;
			case 2: //CPUID_TCM
				asm volatile ("mrc	p15, 0, %0, c0, c0, 2" : "=r" (cpu_id) : : "cc"); break;
			case 3:	//CPUID_TLBTYPE
				asm volatile ("mrc	p15, 0, %0, c0, c0, 3" : "=r" (cpu_id) : : "cc"); break;
			case 4: //CPUID_MPUIR
				asm volatile ("mrc	p15, 0, %0, c0, c0, 4" : "=r" (cpu_id) : : "cc"); break;
			case 5:	//CPUID_MPIDR
				asm volatile ("mrc	p15, 0, %0, c0, c0, 5" : "=r" (cpu_id) : : "cc"); break;
			case 6: //CPUID_REVIDR
				asm volatile ("mrc	p15, 0, %0, c0, c0, 6" : "=r" (cpu_id) : : "cc"); break;
			default: printf("HYPERVISOR READ CPU ID ERROR!\n"); while (1); break;
			}
//			printf("HYPERVISOR READ CPU ID = %x\n", cpu_id);
			*cpuid_out_ptr = cpu_id;
			return;
		}

		case 1047: {		//Read extended CPU ID
			char *ext_reg = (char *) param0;
			unsigned int *__val = (unsigned int *) param1;
			unsigned int ext_id;
			//"c1, 0", "c1, 1", ... "c1, 7"
			if (ext_reg[0] == 'c' && ext_reg[1] == '1' && ext_reg[2] == ',' && ext_reg[3] == ' ') {
				switch (ext_reg[4]) {
				case '0': //CPUID_EXT_PFR0
					asm volatile ("mrc p15,0,%0,c0,c1,0" : "=r" (ext_id) : : "memory"); break;
				case '1': //CPUID_EXT_PFR1
					asm volatile ("mrc p15,0,%0,c0,c1,1" : "=r" (ext_id) : : "memory"); break;
				case '2': //CPUID_EXT_DFR0
					asm volatile ("mrc p15,0,%0,c0,c1,2" : "=r" (ext_id) : : "memory"); break;
				case '3': //CPUID_EXT_AFR0
					asm volatile ("mrc p15,0,%0,c0,c1,3" : "=r" (ext_id) : : "memory"); break;
				case '4': //CPUID_EXT_MMFR0
					asm volatile ("mrc p15,0,%0,c0,c1,4" : "=r" (ext_id) : : "memory"); break;
				case '5': //CPUID_EXT_MMFR1
					asm volatile ("mrc p15,0,%0,c0,c1,5" : "=r" (ext_id) : : "memory"); break;
				case '6': //CPUID_EXT_MMFR2
					asm volatile ("mrc p15,0,%0,c0,c1,6" : "=r" (ext_id) : : "memory"); break;
				case '7': //CPUID_EXT_MMFR3
					asm volatile ("mrc p15,0,%0,c0,c1,7" : "=r" (ext_id) : : "memory"); break;
				default: printf("HYPERVISOR READ EXTENDED CPU ID ERROR!\n"); while (1); break;
				}
			} else if (ext_reg[0] == 'c' && ext_reg[1] == '2' && ext_reg[2] == ',' && ext_reg[3] == ' ') {
				switch (ext_reg[4]) {
				case '0': //CPUID_EXT_ISAR0
					asm volatile ("mrc p15,0,%0,c0,c2,0" : "=r" (ext_id) : : "memory"); break;
				case '1': //CPUID_EXT_ISAR1
					asm volatile ("mrc p15,0,%0,c0,c2,1" : "=r" (ext_id) : : "memory"); break;
				case '2': //CPUID_EXT_ISAR2
					asm volatile ("mrc p15,0,%0,c0,c2,2" : "=r" (ext_id) : : "memory"); break;
				case '3': //CPUID_EXT_ISAR3
					asm volatile ("mrc p15,0,%0,c0,c2,3" : "=r" (ext_id) : : "memory"); break;
				case '4': //CPUID_EXT_ISAR4
					asm volatile ("mrc p15,0,%0,c0,c2,4" : "=r" (ext_id) : : "memory"); break;
				case '5': //CPUID_EXT_ISAR5
					asm volatile ("mrc p15,0,%0,c0,c2,5" : "=r" (ext_id) : : "memory"); break;
				default: printf("HYPERVISOR READ EXTENDED CPU ID ERROR!\n"); while (1); break;
				}
			} else {
				printf("HYPERVISOR READ EXTENDED CPU ID ERROR ARGUMENT: %c%c%c%c%c\n",
						ext_reg[0], ext_reg[1], ext_reg[2], ext_reg[3], ext_reg[4]);
				while (1);
			}
//			printf("HYPERVISOR READ EXTENDED CPU ID = %x\n", ext_id);
			*__val = ext_id;
			return;
		}

		case 1048: {		//Read SCTLR.
			uint32_t cr;
			uint32_t *cr_ptr = (uint32_t *) param0;
			asm volatile ("mrc p15, 0, %0, c1, c0, 0" : "=r" (cr) : : "cc");
//			printf("HYPERVISOR READ SCTLR = %x\n", cr);
			*cr_ptr = cr;
			return;
		}

		case 1049: {		//Set Cache selection register.
			uint32_t *cache_selector = (uint32_t *) param0;
			asm volatile("mcr p15, 2, %0, c0, c0, 0" : : "r" (*cache_selector));
//			printf("HYPERVISOR SETS CACHE SELECTION REGISTER = %x\n", *cache_selector);
			return;
		}

		case 1050: {		//Reads Cache Size ID Register (CCSIDR)
			uint32_t *val = (uint32_t *) param0;
			asm volatile("mrc p15, 1, %0, c0, c0, 0" : "=r" (*val));
//			printf("HYPERVISOR READS CACHE SIZE ID REGISTER = %x\n", *val);
			return;
		}

		case 1051: {	//Reads "ID Code Register", "device ID code that contains information about the processor."
			uint32_t id_code_reg;
			asm volatile ("mrc p15, 0, %0, c0, c0" : "=r" (id_code_reg) : : "cc");
//			printf("HYPERVISOR READS ID Code Register = %x\n", id_code_reg);
			curr_vm->current_mode_state->ctx.reg[9] = id_code_reg;
			return;
		}

		case 1052: {	//Hypercall invoked from assembly code in linux.
			hypercall_cache_op(FLUSH_D_CACHE_AREA, param0, param1);
			return;
		}

		case 1053: {
			//Hypercall 1: Initial virtual section mapping during Linux boot,
			//invoked from head.S.
			uint32_t PAGE_OFFSET = param0;
			uint32_t kernel_sec_start = param1;
			uint32_t kernel_sec_end = param2;
			printf("Hypercall 1: Initial boot virtual Linux map PAGE_OFFSET = %x\n", PAGE_OFFSET);
			printf("Hypercall 1: Initial boot virtual Linux map start va = %x\n", PAGE_OFFSET);
			printf("Hypercall 1: Initial boot virtual Linux map end va = %x\n", PAGE_OFFSET + kernel_sec_end - kernel_sec_start);
			printf("Hypercall 1: Initial boot virtual Linux map start pa = %x\n", kernel_sec_start);
			printf("Hypercall 1: Initial boot virtual Linux map end pa = %x\n", kernel_sec_end);
			linux_boot_virtual_map_section(param0, param1, param2);
			return;
		}

		case 1054: {	//Hypercall 2: Map of DTB.
			printf("Hypercall 2: Linux DTB virtual map fdt_base_pa = %x\n", param0);
			printf("Hypercall 2: Linux DTB virtual map fdt_base_va = %x\n", param1);
			linux_boot_virtual_map_fdt(param0, param1);
			return;
		}

		case 1055: {	//Hypercall 3: Clears page tables.
			printf("Hypercall 3: Linux clear initial mapping: start = 0x%x; end = 0x%x\n", param0, param1);
			linux_clear_virtual_map_section(param0, param1);
			return;
		}

		case 1056: {
			#define L4_34XX_PHYS		0x48000000
			#define L4_WK_AM33XX_PHYS	0x44C00000
			#define CPSW_SS_PHYS		0x4A100000
			#define PRU_ICSS_PHYS		0x4A300000
			#define TPCC_PHYS			0x49000000
			#define TPTC0_PHYS			0x49800000
			#define TPTC1_PHYS			0x49900000
			#define TPTC2_PHYS			0x49A00000
			#define MMCHS2_PHYS			0x47810000
			#define USBSS_PHYS			0x47400000
			#define L3OCMC0_PHYS		0x40300000
			#define EMIF0_PHYS			0x4C000000
			#define GPMC_PHYS			0x50000000
			#define SHAM_PHYS			0x53100000
			#define AES_PHYS			0x53500000
			#define SGX530_PHYS			0x56000000
			if (param1 == L4_34XX_PHYS || param1 == L4_WK_AM33XX_PHYS || param1 == CPSW_SS_PHYS ||
				param1 == PRU_ICSS_PHYS || param1 == TPCC_PHYS || param1 == TPTC0_PHYS ||
				param1 == TPTC1_PHYS || param1 == TPTC2_PHYS || param1 == MMCHS2_PHYS ||
				param1 == USBSS_PHYS || param1 == L3OCMC0_PHYS || param1 == EMIF0_PHYS ||
				param1 == GPMC_PHYS || param1 == SHAM_PHYS || param1 == AES_PHYS ||
				param1 == SGX530_PHYS) {	//Hypercall 4: Maps peripherals on BBB.
				printf("Hypercall 4: Second initial boot virtual Linux I/O map, VA = [0x%x, 0x%x), PA = [0x%x, 0x%x).\n", param0, param0 + param2 - param1, param1, param2);
				check_io_mapping(param0, param1, param2);
			} else {
				//Hypercall 4: ID map of Linux kernel executable code, invoked
				//by arch/arm/mm/idmap.c:idmap_add_pmd. Reuses initial L2 page
				//tables allocated by the hypervisor following immediately the
				//Linux kernel.
				printf("Hypercall 6: Second initial boot virtual Linux section map start va = %x\n", param0);
				printf("Hypercall 6: Second initial boot virtual Linux section map end va = %x\n", param0 + param2 - param1);
				printf("Hypercall 6: Second initial boot virtual Linux section map start pa = %x\n", param1);
				printf("Hypercall 6: Second initial boot virtual Linux section map end pa = %x\n", param2);
				linux_boot_second_virtual_map(param0, param1, param2);
			}
			return;
		}

		case 1057: {	//Reads ACTLR (Auxiliary Control Register)
			uint32_t *aux_cr = (uint32_t *) param0;
            asm("mrc p15, 0, %0, c1, c0, 1" : "=r" (*aux_cr));
//			printf("HYPERVISOR READS Auxiliary Control Register = %x\n", *aux_cr);
			return;
		}

		case 1058: {	//Sets TLS register (TPIDRURO, User Read-Only Thread ID Register, VMSA)
			uint32_t tls = param0;
			asm volatile ("mcr	p15, 0, %0, c13, c0, 3		@ set TLS register" : "=r" (tls) : : "cc");
//			printf("HYPERVISOR SETS TLS Register = %x\n", r4);
			return;
		}

		case 1059: {	//Enable floating point by writing CPACR.
			uint32_t access;
			uint32_t coprocessor10_full_access = 3 << 10*2;
			uint32_t coprocessor11_full_access = 3 << 11*2;
			asm volatile("mrc p15, 0, %0, c1, c0, 2 @ get copro access" : "=r" (access) : : "cc");
			access = access | coprocessor10_full_access | coprocessor11_full_access;
			asm volatile("mcr p15, 0, %0, c1, c0, 2 @ set copro access" : : "r" (access) : "cc");
//			printf("HYPERVISOR ENABLES FULL ACCESS TO COPROCESSORS 10 AND 11\n");
			return;
		}

		case 1060: {	//Reads floating-point associated register.
			uint32_t *val = (uint32_t *) param0;
			uint32_t reg = param1;

			switch (reg) {
			case 0 : asm(".fpu	vfpv2\n"   "vmrs	%0, FPSID" : "=r" (*val) : : "cc"); break;
			case 1 : asm(".fpu	vfpv2\n"   "vmrs	%0, FPSCR" : "=r" (*val) : : "cc"); break;
			case 6 : asm(".fpu	vfpv2\n"   "vmrs	%0, MVFR1" : "=r" (*val) : : "cc"); break;
			case 7 : asm(".fpu	vfpv2\n"   "vmrs	%0, MVFR0" : "=r" (*val) : : "cc"); break;
			case 8 : asm(".fpu	vfpv2\n"   "vmrs	%0, FPEXC" : "=r" (*val) : : "cc"); break;
			case 9 : asm(".fpu	vfpv2\n"   "vmrs	%0, FPINST" : "=r" (*val) : : "cc"); break;
			case 10: asm(".fpu	vfpv2\n"   "vmrs	%0, FPINST2" : "=r" (*val) : : "cc"); break;
			}
//if (reg != 8)
//			printf("Reads floating-point associated register %x: %x\n", reg, *val);
			return;
		}

		case 1061: {	//Writes floating-point associated register.
			uint32_t val = param0;
			uint32_t reg = param1;

			switch (reg) {
			case 0 : asm(".fpu	vfpv2\n"	"vmsr	FPSID, %0" : : "r" (val) : "cc"); break;
			case 1 : asm(".fpu	vfpv2\n"	"vmsr	FPSCR, %0" : : "r" (val) : "cc"); break;
			case 6 : asm(".fpu	vfpv2\n"	"vmsr	MVFR1, %0" : : "r" (val) : "cc"); break;
			case 7 : asm(".fpu	vfpv2\n"	"vmsr	MVFR0, %0" : : "r" (val) : "cc"); break;
			case 8 : asm(".fpu	vfpv2\n"	"vmsr	FPEXC, %0" : : "r" (val) : "cc"); break;
			case 9 : asm(".fpu	vfpv2\n"	"vmsr	FPINST, %0" : : "r" (val) : "cc"); break;
			case 10: asm(".fpu	vfpv2\n"	"vmsr	FPINST2, %0" : : "r" (val) : "cc"); break;
			}
//if (reg != 8)
//			printf("Writes floating-point associated register %x: %x\n", reg, val);
			return;
		}

		case 1062: {	//Checks that DMA re-mapping is not changed.
			uint32_t va = param0;
			uint32_t new_l2e = param1;

			uint32_t l1i = va >> 20;
			uint32_t l1e_va = 0xC0004000 + (l1i << 2);
			uint32_t l1e = *((uint32_t *) l1e_va);
			uint32_t l2_pt_pa = l1e & ~0x3FF;
			uint32_t l2_pt_va = mmu_guest_pa_to_va(l2_pt_pa, curr_vm->config);
			uint32_t l2i = ((va >> 12) & 0xFF) << 2;
			uint32_t l2e = *((uint32_t *)(l2_pt_va + l2i));

			if (l2e & ~0xFFF != new_l2e & ~0xFFF) {
				printf("Hypervisor discovers L2 entry update:\n");
				printf("l1i: 0x%x\n", l1i);
				printf("l1e_va: 0x%x\n", l1e_va);
				printf("l1e: 0x%x\n", l1e);
				printf("l2_pt_pa: 0x%x\n", l2_pt_pa);
				printf("l2_pt_va: 0x%x\n", l2_pt_va);
				printf("l2i: 0x%x\n", l2i);
				printf("l2e: 0x%x\n", l2e);
				printf("Old entry: 0x%x\n", l2e);
				printf("New entry: 0x%x\n", new_l2e);
				while (1);
			}
			printf("Hypervisor 1062 checks DMA re-mapping.\n");
			while (1);
			return;
		}

		case 1063: {	//Sets alignment check enable bit.
			//Only bits 21, 14, 10 and 1 are allowed to be modified by Linux.
			#define SCTLR_A	(1 << 1)
			#define SCTLR_SW (1 << 10)
			#define SCTLR_RR (1 << 14)
			#define SCTLR_FI (1 << 21)
			#define SCTLR_WRITABLE	(SCTLR_FI | SCTLR_RR | SCTLR_SW | SCTLR_A)

			uint32_t sctlr_old;
			asm volatile ("mrc p15, 0, %0, c1, c0, 0" : "=r" (sctlr_old) : : "cc");
			uint32_t sctlr = sctlr_old & ~SCTLR_WRITABLE;
			uint32_t sctlr_mod = param0 & SCTLR_WRITABLE;
			uint32_t sctlr_new = sctlr | sctlr_mod;
			if (sctlr_new != sctlr_old) {
				asm volatile("mcr p15, 0, %0, c1, c0, 0" : : "r" (sctlr_new) : "cc");
				isb();
//				printf("Hypervisor updates: SCTLR to 0x%x\n", sctlr_new);
			}

//			if (sctlr_new != param0) {
//				printf("Linux wants to write 0x%x to SCTLR, and the hypervisor writes 0x%x\n", param0, sctlr_new);
//				while (1);
//		}
			return;
		}

		case 1064: {
			uint32_t fpexc;
			asm(".fpu	vfpv2\n"   "vmrs	%0, FPEXC" : "=r" (fpexc) : : "cc");
//			printf("Hypervisor reads FPEXC = 0x%x\n", fpexc);
			curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[1] = fpexc;
			return;
		}

		case 1065: {
			uint32_t fpexc = curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[5];
//			printf("Hypervisor writes FPEXC = 0x%x\n", fpexc);
			asm(".fpu	vfpv2\n"	"vmsr	FPEXC, %0" : : "r" (fpexc) : "cc");
			return;
		}

		case 1066: {
			uint32_t mvfr0;
			asm(".fpu	vfpv2\n"   "vmrs	%0, MVFR0" : "=r" (mvfr0) : : "cc");
//			printf("Hypervisor reads MVFR0 = 0x%x\n", mvfr0);
			curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[5] = mvfr0;
			return;
		}

		case 1067: {
			uint32_t fpscr = curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[5];
			asm(".fpu	vfpv2\n"	"vmsr	FPSCR, %0" : : "r" (fpscr) : "cc");
//			printf("Hypervisor writes FPSCR = 0x%x\n", fpscr);
			return;
		}

		case 1068: {
			uint32_t fpexc = curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[1];
//			printf("Hypervisor writes FPEXC = 0x%x\n", fpexc);
			asm(".fpu	vfpv2\n"	"vmsr	FPEXC, %0" : : "r" (fpexc) : "cc");
			return;
		}

		case 1069: {	//Reads PMCR, Performance Monitors Control Register, VMSA
			uint32_t *val = (uint32_t *) param0;
			asm volatile("mrc p15, 0, %0, c9, c12, 0" : "=r"(*val));
//			printf("Hypervisor reads PMCR = 0x%x\n", *val);
			return;
		}

		case 1070: {	//Writes PMCNTENCLR, Performance Monitors Count Enable Clear register, VMSA
			uint32_t val = param0;
			asm volatile("mcr p15, 0, %0, c9, c12, 2" : : "r" (val));
//			printf("Hypervisor writes PMCNTENCLR = 0x%x\n", val);
			return;
		}

		case 1071: {
			//Writes PMINTENCLR, Performance Monitors Interrupt Enable Clear
			//register, VMSA, and PMOVSR, Performance Monitors Overflow Flag
			//Status Register, VMSA.
			uint32_t val = param0;
			asm volatile("mcr p15, 0, %0, c9, c14, 2" : : "r" (val));
			isb();
			asm volatile("mcr p15, 0, %0, c9, c12, 3" : : "r" (val));
			isb();
//			printf("Hypervisor writes PMINTENCLR and PMOVSR with: 0x%x\n", val);
			return;
		}

		case 1072: {	//Writes PMCR, Performance Monitors Control Register, VMSA
			uint32_t val = param0;
			isb();
			asm volatile("mcr p15, 0, %0, c9, c12, 0" : : "r"(val));
//			printf("Hypervisor writes PMCR = 0x%x\n", val);
			return;
		}

///////////////////////////////////////////////////////////////////////////////
//		case 1073: {	//TAKEN BY HYPERCALL_UPDATE_PMD_SINGLE
//		}
///////////////////////////////////////////////////////////////////////////////

		case 1074: {	//Reads floating-point associated register from assembly code.
			uint32_t reg = param0;
			uint32_t val;

			switch (reg) {
			case 0 : asm(".fpu	vfpv2\n"   "vmrs	%0, FPSID" : "=r" (val) : : "cc"); break;
			case 1 : asm(".fpu	vfpv2\n"   "vmrs	%0, FPSCR" : "=r" (val) : : "cc"); break;
			case 6 : asm(".fpu	vfpv2\n"   "vmrs	%0, MVFR1" : "=r" (val) : : "cc"); break;
			case 7 : asm(".fpu	vfpv2\n"   "vmrs	%0, MVFR0" : "=r" (val) : : "cc"); break;
			case 8 : asm(".fpu	vfpv2\n"   "vmrs	%0, FPEXC" : "=r" (val) : : "cc"); break;
			case 9 : asm(".fpu	vfpv2\n"   "vmrs	%0, FPINST" : "=r" (val) : : "cc"); break;
			case 10: asm(".fpu	vfpv2\n"   "vmrs	%0, FPINST2" : "=r" (val) : : "cc"); break;
			}

			return;
		}

		case 1075: {	//For allocation of blocks during boot.
			hypercall_map_block(param0, param1);
printf("Hypervisor: Allocation of blocks during boot.\n");
while (1);
			return;
		}

		case 1076: {	//For allocation of blocks during boot, but mapping it as not writable.
printf("Hypervisor: arch/arm/mm.c:early_alloc invoked in Linux\n");
while (1);
			hypercall_map_block_nw(param0, param1);
			return;
		}

		case 1077: {	//NG is false.
			uint32_t start_va = param0;					//Virtual address in kernel 1-1 mapping to map.
			uint32_t end_va = param1;
			uint32_t linux_prot_pte = param2;

			uint32_t vstart = curr_vm->config->firmware->vstart;
			uint32_t pstart = curr_vm->config->firmware->pstart;
			uint32_t psize = curr_vm->config->firmware->psize;
			if (start_va >= end_va) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping but start address (0x%x) greater than or equal to end address (0x%x).\n", start_va, end_va);
				while (1);
			}
			if (start_va < vstart || start_va >= vstart + psize) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping but invalid start address to map: 0x%x.\n", start_va);
				while (1);
			}
			if (end_va < vstart || end_va >= vstart + psize) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping but invalid end address: 0x%x.\n", end_va);
				while (1);
			}
			if (vstart != 0xC0000000) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping but vstart = 0x%x != 0xC0000000\n", vstart);
				while (1);
			}
			if (pstart != 0x81000000) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping but pstart = 0x%x != 0x81000000\n", pstart);
				while (1);
			}
			if (start_va + 0x00200000 < end_va) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping but the range spans more than two MBs: start_va = 0x%x, end_va = 0x%x\n", start_va, end_va);
				while (1);
			}
			if (start_va & 0x00100000 != 0x00100000) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping but the start address is not MB aligned: start_va = 0x%x\n", start_va);
				while (1);
			}
			if (start_va + 0x00100000 != end_va && start_va + 0x00200000 != end_va) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping but range is neither one or two MBs: start_va = 0x%x, end_va = 0x%x\n", start_va, end_va);
				while (1);
			}

//			printf("Hypervisor: Linux kernel is creating 1-1 mapping: start_va = 0x%x, start_pa = 0x%x, table2_pa1 = 0x%x, table2_pa2 = 0x%x.\n", start_va, linux_prot_pte & 0xFFFFF000, pa_to_l2_base_pa(linux_prot_pte & 0xFFFFF000), pa_to_l2_base_pa(linux_prot_pte & 0xFFFFF000) + 0x00100000);

			uint32_t prot = linux_prot_pte & ~0xFFFFF000;
			uint32_t start_pa = linux_prot_pte & 0xFFFFF000;
			if ((start_va - vstart) != (start_pa - pstart)) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping virtual and physical addresses do not correspond to the 1-1 mapping: start_va = 0x%x, start_pa = 0x%x\n", start_va, start_pa);
				while (1);
			}
			uint32_t pfn = linux_prot_pte >> 12;
			uint32_t va = start_va;
			do {
				uint32_t lpte = (pfn << 12) | prot;
				uint32_t hptei = get_pte_hw_i(lpte, 0);
				uint32_t hptec = get_pte_hw_c(lpte, 0);
				if (hptei != hptec) {
					printf("Hypervisor: Linux kernel is creating 1-1 mapping but incorrect computation of hardware page table entry: inline assembly = 0x%x, c implementation = 0x%x.\n", hptei, hptec);
					while (1);
				}
				uint32_t hpte = hptei;
				hpte = adjust_aps(hpte);
				clean_and_invalidate_cache();
				hypercall_dyn_set_pte_one_to_one(va, pfn, lpte, hpte);
				pfn++;
				va += 1 << 12;
			} while (va != end_va);


			uint32_t pa1 = linux_prot_pte & 0xFFFFF000;
			uint32_t pa2 = pa1 + 0x00100000;
			uint32_t l1_pa;
			COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pa);
			uint32_t l1_va = mmu_guest_pa_to_va(l1_pa, curr_vm->config);
			uint32_t l1i = start_va >> 20;
			uint32_t l1e_va1 = l1_va + l1i*4;
			uint32_t l1e_va2 = l1_va + l1i*4 + 4;
			uint32_t l1e1 = *((uint32_t *) l1e_va1);
			uint32_t l1e2 = *((uint32_t *) l1e_va2);
			uint32_t l2_pa1 = pa_to_l2_base_pa(pa1);
			uint32_t l2_pa2 = pa_to_l2_base_pa(pa2);
			uint32_t page_attrs = MMU_L1_TYPE_PT | (HC_DOM_KERNEL << MMU_L1_DOMAIN_SHIFT);

			uint32_t err = dmmu_l1_pt_map(start_va, l2_pa1, page_attrs);
			if (err == ERR_MMU_PT_NOT_UNMAPPED) {
				err = dmmu_unmap_L1_pageTable_entry(start_va);
				if (err) {
					printf("Hypervisor: Linux kernel is creating 1-1 mapping but could not unmap L1 entry: l2_pa1 = 0x%x, err = %d\n", l2_pa1, err);
					while (1);
				}
				err = dmmu_l1_pt_map(start_va, l2_pa1, page_attrs);
			}
			if (err) {
				printf("Hypervisor: Linux kernel is creating 1-1 mapping but could not set L1 entry: l2_pa1 = 0x%x, err = %d\n", l2_pa1, err);
				while (1);
			}

			if (start_va + 0x00200000 == end_va) {	//Map second MB.
				err = dmmu_l1_pt_map(start_va + 0x00100000, l2_pa2, page_attrs);
				if (err == ERR_MMU_PT_NOT_UNMAPPED) {
					err = dmmu_unmap_L1_pageTable_entry(start_va + 0x00100000);
					if (err) {
						printf("Hypervisor: Linux kernel is creating 1-1 mapping but could not unmap L1 entry: l2_pa2 = 0x%x, err = %d\n", l2_pa2, err);
						while (1);
					}
					err = dmmu_l1_pt_map(start_va + 0x00100000, l2_pa2, page_attrs);
				}
				if (err) {
					printf("Hypervisor: Linux kernel is creating 1-1 mapping but could not set L1 entry: l2_pa2 = 0x%x, err = %d\n", l2_pa2, err);
					while (1);
				}
			}

			dsb();
			isb();
			mem_mmu_tlb_invalidate_all(TRUE, TRUE);	//TLB
			mem_cache_invalidate(TRUE, TRUE, TRUE);	//instr, data, writeback

//			printf("Hypervisor: Linux kernel is creating 1-1 mapping return!\n");
			return;
		}

		case 1078: {	//NG is true.
			printf("Hypervisor: Linux kernel is creating 1-1 mapping with NG being true.\n");
			while (1);
//			map_one_to_one_l2(start_va, end_va, linux_prot_pte);
			return;
		}

		case 1079: {	//Hypercall invoked from assembly code in linux for DMA.
			hypercall_cache_op(CLEAN_ENDS_INVALIDATE, param0, param1);
			return;
		}

		case 1080: {		//BPIALL.
			uint32_t val = 0;
			asm volatile("mcr p15, 0, %0, c7, c5, 6" : : "r"(0));
			return;
		}

		case HYPERCALL_CAKEML: {
			uint32_t linux_output_buffer_pa = param0;
			uint32_t linux_input_buffer_pa = param1;
			uint32_t buffer_sizes = param2;
			uint32_t linux_output_buffer_size = buffer_sizes >> 16;
			linux_input_buffer_size = 0x0000FFFF & buffer_sizes;

			uint32_t pstart = curr_vm->config->firmware->pstart;
			uint32_t psize = curr_vm->config->firmware->psize;

			if (linux_output_buffer_pa > linux_output_buffer_pa + linux_output_buffer_size) {
				printf("Linux application output buffer wraps around.\n");
				while (1);
			} else if (linux_output_buffer_pa < pstart) {
				printf("Linux application output buffer start address below Linux memory region.\n");
				while (1);
			} else if (linux_output_buffer_pa + linux_output_buffer_size > pstart + psize) {
				printf("Linux application output buffer end address above Linux memory region.\n");
				while (1);
			}

			if (linux_input_buffer_pa > linux_input_buffer_pa + linux_input_buffer_size) {
				printf("Linux application input buffer wraps around.\n");
				while (1);
			} else if (linux_input_buffer_pa < pstart) {
				printf("Linux application input buffer start address below Linux memory region.\n");
				while (1);
			} else if (linux_input_buffer_pa + linux_input_buffer_size > pstart + psize) {
				printf("Linux application input buffer end address above Linux memory region.\n");
				while (1);
			}

			//Must change DACR so that CakeML memory is accessible to the hypervisor.
			hypercall_rpc();

			char *cakeml_input_buffer = (char *)CAKEML_INPUT_BUFFER_VA;
			linux_input_buffer = (char *) mmu_guest_pa_to_va(linux_input_buffer_pa, curr_vm->config);
			char *linux_output_buffer = (char *) mmu_guest_pa_to_va(linux_output_buffer_pa, curr_vm->config);
			int i;
			for (i = 0; i < linux_output_buffer_size && i < CAKEML_INPUT_BUFFER_SZ; i++)
				cakeml_input_buffer[i] = linux_output_buffer[i];

			return;
		}

		case 1099: {	//Invoked when Linux kernel makes a panic.
			printf("LINUX PANIC!\n");
			while (1);
			return;
		}

		default:
			hypercall_num_error(hypercall_number);
		}
	}
	/*Control of virtual PSR */
#if 1
	if ((curr_vm->current_mode_state->ctx.psr & 0x1F) == 0x13 && curr_vm->current_guest_mode != HC_GM_KERNEL) {	/*virtual SVC mode */
		hyper_panic("PSR in SVC mode but guest mode is not KERNEL\n",
			    0);
	} else if ((curr_vm->current_mode_state->ctx.psr & 0x1F) == 0x10
		   && (curr_vm->current_guest_mode == HC_GM_KERNEL))
		hyper_panic("PSR in USR mode but guest mode is in KERNEL\n", 0);
#endif
}

//addr = IFAR
//status = IFSR
//unused = address of faulting instruction
return_value prefetch_abort_handler(uint32_t addr, uint32_t status, uint32_t unused)
{
#if 1
	if (addr >= 0xc0000000) {
		printf("Pabort: 0x%x Status: 0x%x, u = 0x%x \n", addr, status, unused);
		printf("LR:%x\n", curr_vm->current_mode_state->ctx.lr);
		printf("Guest curr_vm->id %x\n", curr_vm->id);
	}
#endif
	uint32_t interrupted_mode = curr_vm->current_guest_mode;

	/*Need to be in virtual kernel mode to access data abort handler */
	change_guest_mode(HC_GM_KERNEL);
#ifdef LINUX
	/*Set uregs, Linux kernel ususally sets these up in exception vector
	 * which we have to handle now*/

	uint32_t *sp = (uint32_t *) (curr_vm->mode_states[HC_GM_KERNEL].ctx.sp - 72);	/*FRAME_SIZE (18 registers to be saved) */
	uint32_t *context = curr_vm->mode_states[interrupted_mode].ctx.reg;
	uint32_t i;

	for (i = 0; i < 17; i++) {
		*sp++ = *context++;
	}
	*sp = 0xFFFFFFFF;	//ORIG_R0
	curr_vm->mode_states[HC_GM_KERNEL].ctx.sp -= (72);	/*Adjust stack pointer */

	/*Prepare args for prefetchabort handler */
	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[0] = addr;
	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[1] = status;
	/*Linux saves the user registers in the stack */
	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[2] = (uint32_t) curr_vm->mode_states[HC_GM_KERNEL].ctx.sp;

	curr_vm->mode_states[HC_GM_KERNEL].ctx.psr |= IRQ_MASK;	/*Disable IRQ ALWAYS */
	/*Prepare pc for Linux handler */
	uint32_t *pabt_handler = (uint32_t *) (curr_vm->exception_vector[V_PREFETCH_ABORT]);
	if (interrupted_mode == HC_GM_TASK)
		pabt_handler++;	/*DABT_USR located +4 in Linux exception vector */

	curr_vm->current_mode_state->ctx.pc = *pabt_handler;
#endif
	return RV_OK;
}

//addr = DFAR: contains VA of accessed word.
//status = DFSR: contains information about fault.
//unused: contains VA of faulting instruction.
return_value data_abort_handler(uint32_t addr, uint32_t status, uint32_t unused)
{
	uint32_t interrupted_mode = curr_vm->current_guest_mode;

////////
#define CPSW_SS_VIRT 0xFA400000
#define CPSW_SS_SIZE 0x00004000
#define PRU_ICSS_VIRT (CPSW_SS_VIRT + CPSW_SS_SIZE)
#define PRU_ICSS_SIZE 0x00027000
#define TPCC_VIRT (PRU_ICSS_VIRT + PRU_ICSS_SIZE)
#define TPCC_SIZE 0x00001000
#define TPTC0_VIRT (TPCC_VIRT + TPCC_SIZE)
#define TPTC0_SIZE 0x00001000
#define TPTC1_VIRT (TPTC0_VIRT + TPTC0_SIZE)
#define TPTC1_SIZE 0x00001000
#define TPTC2_VIRT (TPTC1_VIRT + TPTC1_SIZE)
#define TPTC2_SIZE 0x00001000
#define MMCHS2_VIRT (TPTC2_VIRT + TPTC2_SIZE)
#define MMCHS2_SIZE 0x00001000
#define USBSS_VIRT (MMCHS2_VIRT + MMCHS2_SIZE)
#define USBSS_SIZE 0x00008000
#define L3OCMC0_VIRT (USBSS_VIRT + USBSS_SIZE)
#define L3OCMC0_SIZE 0x00010000
#define EMIF0_VIRT (L3OCMC0_VIRT + L3OCMC0_SIZE)
#define EMIF0_SIZE 0x00001000
#define GPMC_VIRT (EMIF0_VIRT + EMIF0_SIZE)
#define GPMC_SIZE 0x00001000
#define SHAM_VIRT (GPMC_VIRT + GPMC_SIZE)
#define SHAM_SIZE 0x00001000
#define AES_VIRT (SHAM_VIRT + SHAM_SIZE)
#define AES_SIZE 0x00001000
#define SGX530_VIRT (AES_VIRT + AES_SIZE)
#define SGX530_SIZE 0x00010000
#if defined(LINUX) && defined(CPSW)
	//If accessed address is within the mapped Ethernet Subsystem memory
	//regions.
	if (interrupted_mode == HC_GM_KERNEL && CPSW_SS_VIRT <= addr && addr < CPSW_SS_VIRT + CPSW_SS_SIZE) {
//		printf("Hypervisor: CPSW ACCESS!\n");
		//Checks the access. If it is valid it is carried out, otherwise a
		//message is printed and the system freezes.
		BOOL ret = soc_check_cpsw_access(addr, curr_vm->current_mode_state->ctx.pc);

		//If the access is invalid the system freezes.
		if (!ret) {
			printf("Hypervisor: FAILURE AT CPSW DRIVER!\n");
			for (;;) ;
		}
		//Increment program counter to point to instruction following the
		//failing one.
		curr_vm->current_mode_state->ctx.pc += 4;

		//Returns to exception_bottom which restores the guest to exeucte the
		//instruction following the failed one.
		return RV_OK;
	} else if (interrupted_mode == HC_GM_KERNEL && TPCC_VIRT <= addr && addr < TPCC_VIRT + TPCC_SIZE) {
//		printf("Hypervisor: TPCC ACCESS at 0x%x!\n", addr - TPCC_VIRT);
		while (1);
	} else if (interrupted_mode == HC_GM_KERNEL && TPTC0_VIRT <= addr && addr < TPTC0_VIRT + TPTC0_SIZE) {
//		printf("Hypervisor: TPTC0 ACCESS at 0x%x!\n", addr - TPTC0_VIRT);
		BOOL ret = soc_check_tptc0_access(addr, curr_vm->current_mode_state->ctx.pc);
		if (!ret) {
			printf("Hypervisor: FAILURE AT TPTC0 DRIVER!\n");
			while (1);
		} else {
//			printf("Hypervisor: SUCCESS AT TPTC0 DRIVER!\n");
			curr_vm->current_mode_state->ctx.pc += 4;
			return RV_OK;
		}
	} else if (interrupted_mode == HC_GM_KERNEL && TPTC1_VIRT <= addr && addr < TPTC1_VIRT + TPTC1_SIZE) {
//		printf("Hypervisor: TPTC1 ACCESS at 0x%x!\n", addr - TPTC1_VIRT);
		BOOL ret = soc_check_tptc1_access(addr, curr_vm->current_mode_state->ctx.pc);
		if (!ret) {
			printf("Hypervisor: FAILURE AT TPTC1 DRIVER!\n");
			while (1);
		} else {
//			printf("Hypervisor: SUCCESS AT TPTC1 DRIVER!\n");
			curr_vm->current_mode_state->ctx.pc += 4;
			return RV_OK;
		}
	} else if (interrupted_mode == HC_GM_KERNEL && TPTC2_VIRT <= addr && addr < TPTC2_VIRT + TPTC2_SIZE) {
//		printf("Hypervisor: TPTC2 ACCESS at 0x%x!\n", addr - TPTC2_VIRT);
		BOOL ret = soc_check_tptc2_access(addr, curr_vm->current_mode_state->ctx.pc);
		if (!ret) {
			printf("Hypervisor: FAILURE AT TPTC2 DRIVER!\n");
			while (1);
		} else {
//			printf("Hypervisor: SUCCESS AT TPTC2 DRIVER!\n");
			curr_vm->current_mode_state->ctx.pc += 4;
			return RV_OK;
		}
	}
#endif

#define AM33XX_L4_WK_IO_OFFSET	0xb5000000
#define CM_PHYS					0x44E10000
#define CM_SIZE					0x2000
#define CM_VIRT					(CM_PHYS + AM33XX_L4_WK_IO_OFFSET)
#define CM_OFFSET(va)			(va - CM_VIRT)
	//Trap and emulate writes to the control module, since they can only be written in privileged mode.
	if (interrupted_mode == HC_GM_KERNEL && CM_VIRT <= addr && addr < CM_VIRT + CM_SIZE) {
//		printf("CONTROL MODULE TRAP: Write to location at va = %x, pa = 0x%x, pc = 0x%x.\n", addr, addr - AM33XX_L4_WK_IO_OFFSET, curr_vm->current_mode_state->ctx.pc);
		if (addr == CM_OFFSET(0x620))
			printf("CONTROL MODULE TRAP: Write to USB_CTRL0\n");
		else if (addr == CM_OFFSET(0x624))
			printf("CONTROL MODULE TRAP: Write to USB_STS0\n");
		else if (addr == CM_OFFSET(0x628))
			printf("CONTROL MODULE TRAP: Write to USB_CTRL1\n");
		else if (addr == CM_OFFSET(0x62C))
			printf("CONTROL MODULE TRAP: Write to USB_STS1\n");
		else if (addr == CM_OFFSET(0x648))
			printf("CONTROL MODULE TRAP: Write to USB_WKUP_CTRL\n");
		else if (addr == CM_OFFSET(0xA1C))
			printf("CONTROL MODULE TRAP: Write to CONF_USB0_DRVVBUS\n");
		else if (addr == CM_OFFSET(0xA34))
			printf("CONTROL MODULE TRAP: Write to CONF_USB1_DRVVBUS\n");

		uint32_t instruction_encoding = *((uint32_t *) curr_vm->current_mode_state->ctx.pc);
		uint32_t *context, t, n, imm, rt, rn;

		//Checks the type of instruction that was executed and takes appropriate
		//actions.
		//STR  Rt, [Rn, #+imm32] = mem32[Regs[Rn] + imm32] := Regs[Rt]
		if ((0xFFF00000 & instruction_encoding) == 0xE5800000) {
			//Retrieves the source register indexes and the store address
			//offset.
			t = (0x0000F000 & instruction_encoding) >> 12;
			n = (0x000F0000 & instruction_encoding) >> 16;
			imm = 0x00000FFF & instruction_encoding;

			//Retrieves the contents of the registers that are used when
			//the instruction is to be re-executed. The address base register
			//is set to its original value added with the address offset.
			context = curr_vm->current_mode_state->ctx.reg;
			rt = *(context + t);
			rn = *(context + n) + imm;

			//If the memory location to store a value to differs from what was
			//reported by the MMU, then there is some bug.
			if (rn != addr) {
				printf("CONTROL MODULE TRAP: Base register Regs[R%d] = %x distinct from written location at %x\n", n, rn, addr);
				while (1);
			} else {	//Re-execute write.
				*((volatile uint32_t *) rn) = rt;
				//Increment program counter to point to instruction following the
				//failing one.
				curr_vm->current_mode_state->ctx.pc += 4;
				return RV_OK;
			}
		} else {
			printf("CONTROL MODULE TRAP ERROR: UNKNOWN INSTRUCTION (0x%x at 0x%x) WRITING CONTROL MODULE REGISTER: 0x%x\n", instruction_encoding, unused, addr);
			while (1);
		}
	}

#define L4_34XX_BASE		0x48000000
#define OMAP2_L4_IO_OFFSET	0xB2000000
#define L4_PER_VIRT			(L4_34XX_BASE + OMAP2_L4_IO_OFFSET)
#define McSPI0_OFFSET		0x00030000
#define McSPI0_PHYS			(L4_34XX_BASE + McSPI0_OFFSET)
#define McSPI0_SIZE			PAGE_SIZE
#define McSPI0_VIRT			(McSPI0_PHYS + OMAP2_L4_IO_OFFSET)
#define McSPI0_MCSPI_REVISION	(McSPI0_VIRT + 0x000)
#define McSPI0_MCSPI_SYSCONFIG	(McSPI0_VIRT + 0x110)
#define McSPI0_MCSPI_SYSSTATUS	(McSPI0_VIRT + 0x114)
#define I2C2_OFFSET			0x0019C000
#define I2C2_PHYS			(L4_34XX_BASE + I2C2_OFFSET)
#define I2C2_SIZE			PAGE_SIZE
#define I2C2_VIRT			(I2C2_PHYS + OMAP2_L4_IO_OFFSET)
	//First 2 MB of L4_PER are inaccessible.
	if (interrupted_mode == HC_GM_KERNEL && L4_PER_VIRT <= addr && addr < L4_PER_VIRT + 2*SECTION_SIZE) {
		if (McSPI0_VIRT <= addr && addr < McSPI0_VIRT + McSPI0_SIZE) {
			uint32_t instruction_encoding = *((uint32_t *) curr_vm->current_mode_state->ctx.pc);
			uint32_t *context, t, n, rt, rn;
			if ((addr == McSPI0_MCSPI_REVISION || addr == McSPI0_MCSPI_SYSCONFIG || addr == McSPI0_MCSPI_SYSSTATUS) &&
				((instruction_encoding & 0xFFF00FFF) == 0xE5900000)) {
//printf("Hypervisor1: Linux accessed unallowed McSPI0 register at 0x%x with instruction at 0x%x\n", addr - McSPI0_VIRT + McSPI0_PHYS, unused);
				t = (0x0000F000 & instruction_encoding) >> 12;
				n = (0x000F0000 & instruction_encoding) >> 16;
				context = curr_vm->current_mode_state->ctx.reg;
				rn = *(context + n);							//Register with address.
				*(context + t) = *((volatile uint32_t *) rn);	//Register with result.
				curr_vm->current_mode_state->ctx.pc += 4;
				return RV_OK;
			} else if ((addr == McSPI0_MCSPI_REVISION || addr == McSPI0_MCSPI_SYSCONFIG || addr == McSPI0_MCSPI_SYSSTATUS) &&
				((instruction_encoding & 0xFFF00FFF) == 0xE5800000)) {
//printf("Hypervisor2: Linux accessed unallowed McSPI0 register at 0x%x with instruction at 0x%x\n", addr - McSPI0_VIRT + McSPI0_PHYS, unused);
				t = (0x0000F000 & instruction_encoding) >> 12;
				n = (0x000F0000 & instruction_encoding) >> 16;
				context = curr_vm->current_mode_state->ctx.reg;
				rt = *(context + t);							//Register with data.
				rn = *(context + n);							//Register with address.
				*((volatile uint32_t *) rn) = rt;
				curr_vm->current_mode_state->ctx.pc += 4;
				return RV_OK;
			} else {
				printf("Hypervisor3: Linux accessed unallowed McSPI0 register at 0x%x with instruction at 0x%x\n", addr - McSPI0_VIRT + McSPI0_PHYS, unused);
				while (1);
			}
		} else if (I2C2_VIRT <= addr && addr < I2C2_VIRT + I2C2_SIZE) {
#define I2C_REVNB_LO_OFFSET	0x0
#define I2C_REVNB_LO_VIRT	(I2C2_VIRT + I2C_REVNB_LO_OFFSET)
#define I2C_REVNB_HI_OFFSET	0x4
#define I2C_REVNB_HI_VIRT	(I2C2_VIRT + I2C_REVNB_HI_OFFSET)
#define I2C_SYSC_OFFSET		0x10
#define I2C_SYSC_VIRT		(I2C2_VIRT + I2C_SYSC_OFFSET)
#define I2C_IRQSTATUS_OFFSET	0x28
#define I2C_IRQSTATUS_VIRT	(I2C2_VIRT + I2C_IRQSTATUS_OFFSET)
#define I2C_IRQENABLE_SET_OFFSET	0x2C
#define I2C_IRQENABLE_SET_VIRT		(I2C2_VIRT + I2C_IRQENABLE_SET_OFFSET)
#define I2C_IRQENABLE_CLR_OFFSET	0x30
#define I2C_IRQENABLE_CLR_VIRT		(I2C2_VIRT + I2C_IRQENABLE_CLR_OFFSET)
#define I2C_WE_OFFSET		0x34
#define I2C_WE_VIRT			(I2C2_VIRT + I2C_WE_OFFSET)
#define I2C_CON_OFFSET		0xA4
#define I2C_CON_VIRT		(I2C2_VIRT + I2C_CON_OFFSET)
#define I2C_SYSS_OFFSET		0x90
#define I2C_SYSS_VIRT		(I2C2_VIRT + I2C_SYSS_OFFSET)
#define I2C_BUFSTAT_OFFSET	0xC0
#define I2C_BUFSTAT_VIRT	(I2C2_VIRT + I2C_BUFSTAT_OFFSET)
#define I2C_PSC_OFFSET		0xB0
#define I2C_PSC_VIRT		(I2C2_VIRT + I2C_PSC_OFFSET)
#define I2C_SCLL_OFFSET		0xB4
#define I2C_SCLL_VIRT		(I2C2_VIRT + I2C_SCLL_OFFSET)
#define I2C_SCLH_OFFSET		0xB8
#define I2C_SCLH_VIRT		(I2C2_VIRT + I2C_SCLH_OFFSET)
			uint32_t instruction_encoding = *((uint32_t *) curr_vm->current_mode_state->ctx.pc);
			uint32_t *context, t, n, rt, rn;

			if ((addr == I2C_REVNB_LO_VIRT || addr == I2C_REVNB_HI_VIRT || addr == I2C_SYSC_VIRT || addr == I2C_CON_VIRT ||
				 addr == I2C_SYSS_VIRT || addr == I2C_BUFSTAT_VIRT || addr == I2C_IRQENABLE_SET_VIRT ||
				 addr == I2C_IRQSTATUS_VIRT) &&
				(0xFFF00FFF & instruction_encoding) == 0xE1D000B0) {
				t = (0x0000F000 & instruction_encoding) >> 12;	//Destination register.
				n = (0x000F0000 & instruction_encoding) >> 16;
				context = curr_vm->current_mode_state->ctx.reg;
				rn = *(context + n);				//Source register.
				asm volatile("ldrh %0, [%1]" : "=r"(rt) : "r"(rn));
				*(context + t) = rt;				//Destination register.
				curr_vm->current_mode_state->ctx.pc += 4;
				return RV_OK;
			} else if ((addr == I2C_SYSC_VIRT || addr == I2C_CON_VIRT || addr == I2C_PSC_VIRT || addr == I2C_SCLL_VIRT ||
						addr == I2C_SCLH_VIRT || addr == I2C_WE_VIRT || addr == I2C_IRQENABLE_SET_VIRT ||
						addr == I2C_IRQENABLE_CLR_VIRT || addr == I2C_IRQSTATUS_VIRT) &&
				(0xFFF00FFF & instruction_encoding) == 0xE1C000B0) {
				t = (0x0000F000 & instruction_encoding) >> 12;	//Destination register.
				n = (0x000F0000 & instruction_encoding) >> 16;
				context = curr_vm->current_mode_state->ctx.reg;
				rt = *(context + t);
				rn = *(context + n);
//				printf("Hypervisor4: Linux strh 0x%x at I2C_SYSC at 0x%x\n", rt, rn);
//				while (1);
				asm volatile("strh %0, [%1]" : : "r"(rt), "r"(rn));
				curr_vm->current_mode_state->ctx.pc += 4;
				return RV_OK;
			} else {
				printf("Hypervisor4: Linux accessed unallowed I2C2 register at 0x%x with instruction at 0x%x (0x%x)\n", addr - I2C2_VIRT + I2C2_PHYS, unused, instruction_encoding);
				while (1);
			}
		} else {
			uint32_t instruction_encoding = *((uint32_t *) curr_vm->current_mode_state->ctx.pc);
			uint32_t *context, t, n, imm, rt, rn;

			if ((0xFFF00000 & instruction_encoding) == 0xE5800000) {
				t = (0x0000F000 & instruction_encoding) >> 12;
				n = (0x000F0000 & instruction_encoding) >> 16;
				imm = 0x00000FFF & instruction_encoding;
				context = curr_vm->current_mode_state->ctx.reg;
				rt = *(context + t);
				rn = *(context + n) + imm;
				*((volatile uint32_t *) rn) = rt;
				curr_vm->current_mode_state->ctx.pc += 4;
				return RV_OK;
			} else if ((0xFFF00000 & instruction_encoding) == 0xE5900000) {
				t = (0x0000F000 & instruction_encoding) >> 12;	//Destination register.
				n = (0x000F0000 & instruction_encoding) >> 16;
				imm = 0x00000FFF & instruction_encoding;
				context = curr_vm->current_mode_state->ctx.reg;
				rn = *(context + n);				//Register with address.
				rt = *((volatile uint32_t *) (((uint32_t) rn) + imm));	//Register to store load result.
				*(context + t) = rt;				//Store result so that return handler loads register with correct value.
				curr_vm->current_mode_state->ctx.pc += 4;
				return RV_OK;
			} else if ((0xFFF00FFF & instruction_encoding) == 0xE1D000B0) {
				t = (0x0000F000 & instruction_encoding) >> 12;	//Destination register.
				n = (0x000F0000 & instruction_encoding) >> 16;
				context = curr_vm->current_mode_state->ctx.reg;
				rn = *(context + n);				//Source register.
				asm volatile("ldrh %0, [%1]" : "=r"(rt) : "r"(rn));
				*(context + t) = rt;				//Destination register.
				curr_vm->current_mode_state->ctx.pc += 4;
				return RV_OK;
			} else if ((0xFFF00FFF & instruction_encoding) == 0xE1C000B0) {
				t = (0x0000F000 & instruction_encoding) >> 12;	//Destination register.
				n = (0x000F0000 & instruction_encoding) >> 16;
				context = curr_vm->current_mode_state->ctx.reg;
				rt = *(context + t);
				rn = *(context + n);
				asm volatile("strh %0, [%1]" : : "r"(rt), "r"(rn));
				curr_vm->current_mode_state->ctx.pc += 4;
				return RV_OK;
			} else {
				printf("L4_PER TRAP: Unknown instruction 0x%x at 0x%x with status = 0x%x\n", instruction_encoding, unused, status);
				while (1);
			}
		}
	} else if (interrupted_mode == HC_GM_TRUSTED && McSPI0_VIRT <= addr && addr < McSPI0_VIRT + McSPI0_SIZE) {
//		uint32_t dacr;
//		COP_READ(COP_SYSTEM, COP_SYSTEM_DOMAIN, dacr);
//		uint32_t *table1 = flpt_va;
//		uint32_t index = MMU_L1_INDEX(McSPI0_VIRT);
//		uint32_t val = table1[index];
//		printf("L4_PER TRAP: Trusted guest attempts to access SPI register at 0x%x with instruction at 0x%x with DACR = 0x%x, val = 0x%x, status = 0x%x\n", addr - McSPI0_VIRT + McSPI0_PHYS, unused, dacr, val, status);

		//Trusted guest attempts to write camera.
		uint32_t instruction_encoding = *((uint32_t *) curr_vm->current_mode_state->ctx.pc);
		uint32_t *context, t, n, rt, rn;
		if ((instruction_encoding & 0xFFF00FFF) == 0xE5800000) {//e58nt000 	str	rt, [rn]
			t = (0x0000F000 & instruction_encoding) >> 12;
			n = (0x000F0000 & instruction_encoding) >> 16;
			context = curr_vm->current_mode_state->ctx.reg;
			rt = *(context + t);							//Register with data.
			rn = *(context + n);							//Register with address.
			*((volatile uint32_t *) rn) = rt;
			curr_vm->current_mode_state->ctx.pc += 4;
			return RV_OK;
		} else if ((instruction_encoding & 0xFFF00FFF) == 0xE5900000) {	//ldr rt, [rn]
			t = (0x0000F000 & instruction_encoding) >> 12;
			n = (0x000F0000 & instruction_encoding) >> 16;
			context = curr_vm->current_mode_state->ctx.reg;
			rn = *(context + n);							//Register with address.
			*(context + t) = *((volatile uint32_t *) rn);	//Register with result.
			curr_vm->current_mode_state->ctx.pc += 4;
			return RV_OK;
		} else {
			printf("L4_PER TRAP: Trusted guest attempted to access unsupported SPI register access (0x%x) at 0x%x with instruction at 0x%x\n", instruction_encoding, addr - McSPI0_VIRT + McSPI0_PHYS, unused);
			while (1);
		}
	} else if (interrupted_mode == HC_GM_TRUSTED && I2C2_VIRT <= addr && addr < I2C2_VIRT + I2C2_SIZE) {
		//Trusted guest attempts to write (initialize due to I2C?) camera.
		uint32_t instruction_encoding = *((uint32_t *) curr_vm->current_mode_state->ctx.pc);
		uint32_t *context, t, n, rt, rn;

		if ((instruction_encoding & 0xFFF00FFF) == 0xE5800000) {//e58nt000 	str	rt, [rn]
			t = (0x0000F000 & instruction_encoding) >> 12;
			n = (0x000F0000 & instruction_encoding) >> 16;
			context = curr_vm->current_mode_state->ctx.reg;
			rt = *(context + t);							//Register with data.
			rn = *(context + n);							//Register with address.
			*((volatile uint32_t *) rn) = rt;
			curr_vm->current_mode_state->ctx.pc += 4;
			return RV_OK;
		} else if ((instruction_encoding & 0xFFF00FFF) == 0xE5900000) {	//ldr rt, [rn]
			t = (0x0000F000 & instruction_encoding) >> 12;
			n = (0x000F0000 & instruction_encoding) >> 16;
			context = curr_vm->current_mode_state->ctx.reg;
			rn = *(context + n);							//Register with address.
			*(context + t) = *((volatile uint32_t *) rn);	//Register with result.
			curr_vm->current_mode_state->ctx.pc += 4;
			return RV_OK;
		} else {
			printf("L4_PER TRAP: Trusted guest attempted to access unsupported I2C register access (0x%x) at 0x%x with instruction at 0x%x\n", instruction_encoding, addr - I2C2_VIRT + I2C2_PHYS, unused);
			while (1);
		}
	} else if (interrupted_mode == HC_GM_TRUSTED) {
		printf("Hypervisor: Trusted guest caused unknown data abort when accessing register 0x%x with instruction at 0x%x\n", addr, unused);
		while (1);
	}

#define FS4(DFSR)	(DFSR & 0x400)
#define FS30(DFSR)	(DFSR & 0xF)
#define FS(DFSR)	((FS4(DFSR) >> 6) | FS30(DFSR))

	BOOL emulated = FALSE;
	if (interrupted_mode == HC_GM_KERNEL && addr < HAL_VIRT_START && FS(status) != 0x1) {	//Do not emulate alignment faults.
//		printf("Dabort: Tries to emulate access to 0x%x when executing instruction at 0x%x.\n", addr, unused);
		emulated = emulate_write(addr, unused);
	}

	if (emulated) {
//		printf("Dabort: Emulated access to 0x%x now made writable when executing instruction at 0x%x.\n", addr, unused);
		return RV_OK;	//Do not propagate error to Linux, but let Linux reexecute the instruction and continue to execute as if the exception had not happen.
//		while (1);
	}



/*
	if (addr >= 0xC0000000) {
		printf("DAFR: 0x%x DFSR: 0x%x, VA OF INST = 0x%x with code 0x%x\n", addr, status, unused, *((uint32_t *) (unused)));
		printf("Accessing MB %d/0x%x\n", addr >> 20, addr >> 20);
		uint32_t l1_pt_pa;
		COP_READ(COP_SYSTEM, COP_SYSTEM_TRANSLATION_TABLE0, l1_pt_pa);
		uint32_t va;
		for (va = CPSW_SS_VIRT; va < SGX530_VIRT + SGX530_SIZE; va += SECTION_SIZE) {
			uint32_t l1i = va >> 20;
			uint32_t l1e_pa = (l1_pt_pa & 0xFFFFC000) | (l1i << 2);
			uint32_t l1e_va = mmu_guest_pa_to_va(l1e_pa, curr_vm->config);
			uint32_t l1e = *((uint32_t *) l1e_va);
			printf("Hypervisor l1[%d/0x%x] = 0x%x\n", l1i, l1i, l1e);
		}

		uint32_t l1i = addr >> 20;
		uint32_t l1e_pa = (l1_pt_pa & 0xFFFFC000) | (l1i << 2);
		uint32_t l1e_va = mmu_guest_pa_to_va(l1e_pa, curr_vm->config);
		uint32_t l1e = *((uint32_t *) l1e_va);

		uint32_t l2i = (addr & 0x000FF000) >> 12;
		uint32_t l2e_pa = (l1e & 0xFFFFFC00) | (l2i << 2);
		uint32_t l2e_va = GET_VIRT(l2e_pa);
		uint32_t l2e = *((uint32_t *) l2e_va);

		printf("Hypervisor l2[%d/0x%x] = 0x%x\n", l2i, l2i, l2e);

		while (1);
	}
*/
////////
	/*Must be in virtual kernel mode to access kernel handlers */
	change_guest_mode(HC_GM_KERNEL);
#ifdef LINUX

	/*Set uregs, Linux kernel ususally sets these up in exception vector
	 * which we have to handle now*/

	uint32_t *sp = (uint32_t *) (curr_vm->mode_states[HC_GM_KERNEL].ctx.sp - 72);	/*FRAME_SIZE (18 registers to be saved) */
	uint32_t *context = curr_vm->mode_states[interrupted_mode].ctx.reg;
	uint32_t i;

	/*Save context in sp */
	for (i = 0; i < 17; i++) {
		*sp++ = *context++;
	}
	*sp = 0xFFFFFFFF;	//ORIG_R0
	curr_vm->mode_states[HC_GM_KERNEL].ctx.sp -= (72);	/*Adjust stack pointer */

	/*Prepare args for dataabort handler */
	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[0] = addr;
	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[1] = status;
	/*Linux saves the user registers in the stack */
	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[5] = (uint32_t) curr_vm->mode_states[HC_GM_KERNEL].ctx.psr;	/*spsr in r5 for linux kernel vector */

	curr_vm->mode_states[HC_GM_KERNEL].ctx.psr |= IRQ_MASK;	/*Disable IRQ ALWAYS */

	/*Prepare pc for handler and lr to return from handler */

	uint32_t *dabt_handler =
	    (uint32_t *) (curr_vm->exception_vector[V_DATA_ABORT]);
	if (interrupted_mode == HC_GM_TASK) {
////////
//    printf("HYPERVISOR: core/hypervisor/handlers.c:data_abort_handler(): The data abort occurred in a task!\n");
////////
		dabt_handler++;	//DABT_USR located +4
	}
////////
//  else {
//    printf("HYPERVISOR: core/hypervisor/handlers.c:data_abort_handler(): The data abort occurred in the kernel!\n");
//  }
////////

	curr_vm->current_mode_state->ctx.pc = *dabt_handler;
#if 0	 /*DEBUG*/
////////
	    //   printf("Task PC:%x LR:%x \n",curr_vm->mode_states[HC_GM_TASK].ctx.pc, curr_vm->mode_states[HC_GM_TASK].ctx.lr);
////////
	    printf("Kernel PC:%x LR:%x \n",
		   curr_vm->mode_states[HC_GM_KERNEL].ctx.pc,
		   curr_vm->mode_states[HC_GM_KERNEL].ctx.lr);
#endif
#endif
	return RV_OK;
}

#define LINUX_5_15_13
#ifndef LINUX_5_15_13
return_value irq_handler(uint32_t irq, uint32_t r1, uint32_t r2)
{
//	printf("IRQ handler called %d, interrupt handler: 0x%x\n", irq, );
	if (curr_vm->current_mode_state->ctx.psr & 0x80) {	/*Interrupts are off, return */
		printf("Interrupt: FREEZE!\n");
		for (;;) ;
//              mask_interrupt(irq, 1); //Mask interrupt and mark pending
		return RV_OK;
	}

	uint32_t interrupted_mode = curr_vm->current_guest_mode;
	change_guest_mode(HC_GM_KERNEL);
#ifdef LINUX
	/*Prepare stack for nested irqs */
	uint32_t i;

	uint32_t *context = curr_vm->mode_states[interrupted_mode].ctx.reg;
	uint32_t *sp_push = (uint32_t *) (curr_vm->mode_states[HC_GM_KERNEL].ctx.sp - 72);	//FRAME_SIZE (18 registers to be saved)

	for (i = 0; i < 17; i++) {
		*sp_push++ = *context++;
	}
	*sp_push = 0xFFFFFFFF;	//ORIG_R0
	curr_vm->mode_states[HC_GM_KERNEL].ctx.sp -= (72);	//FRAME_SIZE (18 registers to be saved)

#if 0	 /*DEBUG*/
	    printf("IRQ handler called %x:%x:\n", irq,
		   curr_vm->mode_states[HC_GM_KERNEL].ctx.sp);
#endif
	curr_vm->interrupted_mode = interrupted_mode;

	curr_vm->current_mode_state->ctx.reg[0] = irq;
	curr_vm->current_mode_state->ctx.reg[1] = curr_vm->mode_states[HC_GM_KERNEL].ctx.sp;
	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[5] = (uint32_t) curr_vm->mode_states[HC_GM_KERNEL].ctx.psr;	/*spsr in r5 for linux kernel vector */

	uint32_t *irq_handler = (uint32_t *) (curr_vm->exception_vector[V_IRQ]);

	if (interrupted_mode == HC_GM_TASK)
		irq_handler++;	//IRQ_USR located +4
	printf("IRQ TEST %d, interrupt handler: 0x%x\n", irq, irq_handler);
	printf("IRQ handler called %d, interrupt handler: 0x%x\n", irq, irq_handler);
	printf("IRQ TEST %d, interrupt handler: 0x%x\n", irq, irq_handler);
	curr_vm->current_mode_state->ctx.pc = *irq_handler;
	curr_vm->current_mode_state->ctx.psr |= IRQ_MASK;
	curr_vm->current_mode_state->ctx.sp = curr_vm->mode_states[HC_GM_KERNEL].ctx.sp;

#endif
//      unmask_interrupt(irq, 0);
	return RV_OK;
}
#else
static int counter = 0;
return_value irq_handler(uint32_t irq, uint32_t r1, uint32_t r2)
{
//if (print_pc) {
//counter++;
//	if (counter % 100 == 0)
//		printf("INTERRUPT: 0x%x\n", curr_vm->current_mode_state->ctx.pc);
//}

	if (curr_vm->current_mode_state->ctx.psr & 0x80) {	/*Interrupts are off, return */
		printf("INTERRUPT: FREEZE!\n");
		for (;;) ;
//              mask_interrupt(irq, 1); //Mask interrupt and mark pending
		return RV_OK;
	}

	uint32_t interrupted_mode = curr_vm->current_guest_mode;
	change_guest_mode(HC_GM_KERNEL);
#ifdef LINUX
	/*Prepare stack for nested irqs */
	uint32_t i;

	uint32_t *context = curr_vm->mode_states[interrupted_mode].ctx.reg;
	uint32_t *sp_push = (uint32_t *) (curr_vm->mode_states[HC_GM_KERNEL].ctx.sp - 72);	//FRAME_SIZE (18 registers to be saved)

	for (i = 0; i < 17; i++) {
		*sp_push++ = *context++;
	}
	*sp_push = 0xFFFFFFFF;	//ORIG_R0
	curr_vm->mode_states[HC_GM_KERNEL].ctx.sp -= (72);	//FRAME_SIZE (18 registers to be saved)

	curr_vm->interrupted_mode = interrupted_mode;

//	curr_vm->current_mode_state->ctx.reg[0] = curr_vm->mode_states[HC_GM_KERNEL].ctx.sp;
//	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[5] = (uint32_t) curr_vm->mode_states[HC_GM_KERNEL].ctx.psr;	/*spsr in r5 for linux kernel vector */

	uint32_t *irq_handler = (uint32_t *) (curr_vm->exception_vector[V_IRQ]);

	if (interrupted_mode == HC_GM_TASK)
		irq_handler++;	//IRQ_USR located +4

	curr_vm->current_mode_state->ctx.pc = *irq_handler;
	curr_vm->current_mode_state->ctx.psr |= IRQ_MASK;
	curr_vm->current_mode_state->ctx.sp = curr_vm->mode_states[HC_GM_KERNEL].ctx.sp;

#endif
//      unmask_interrupt(irq, 0);
	return RV_OK;
}
#endif

/*Used for floating point emulation in Linux*/
return_value undef_handler(uint32_t instr, uint32_t unused, uint32_t addr)
{
#if 0	//floating point
	printf("Undefined abort\n Address: 0x%x Instruction: 0x%x \n", addr, instr);
#endif
	uint32_t interrupted_mode = curr_vm->current_guest_mode;

	/*Must be in virtual kernel mode to access kernel handlers */
	change_guest_mode(HC_GM_KERNEL);
#ifdef LINUX
	/*Set uregs, Linux kernel ususally sets these up in exception vector
	 * which we have to handle now*/

	uint32_t *sp = (uint32_t *) (curr_vm->mode_states[HC_GM_KERNEL].ctx.sp - 72);	//FRAME_SIZE (18 registers to be saved)
	uint32_t *context = curr_vm->mode_states[interrupted_mode].ctx.reg;
	uint32_t i;

	for (i = 0; i < 17; i++) {
		*sp++ = *context++;
	}
	*sp = 0xFFFFFFFF;	//ORIG_R0
	curr_vm->mode_states[HC_GM_KERNEL].ctx.sp -= (72);	//FRAME_SIZE (18 registers to be saved)
	//Context saved in sp

	/*Prepare args for dataabort handler */
	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[4] = curr_vm->mode_states[interrupted_mode].ctx.pc;
	curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[5] = curr_vm->mode_states[interrupted_mode].ctx.psr;	/*spsr in r5 for linux kernel vector */

	/*Linux saves the user registers in the stack */
	curr_vm->mode_states[HC_GM_KERNEL].ctx.psr |= IRQ_MASK;	/*Disable IRQ ALWAYS */

	uint32_t *und_handler = (uint32_t *) (curr_vm->exception_vector[V_UNDEF]);
	if (interrupted_mode == HC_GM_TASK)
		und_handler++;	//DABT_USR located +4

	curr_vm->current_mode_state->ctx.pc = *und_handler;
#endif
	return RV_OK;
}
