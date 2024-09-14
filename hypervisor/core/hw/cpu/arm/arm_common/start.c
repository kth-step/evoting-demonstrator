#include "hyper.h"
#include "guest_blob.h"
#include<cache.h>

extern virtual_machine *curr_vm;

void start()
{
	uint32_t r3 = curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[3];
	uint32_t r4 = curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[4];
	uint32_t r5 = curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[5];
	uint32_t r6 = curr_vm->mode_states[HC_GM_KERNEL].ctx.reg[6];
	curr_vm->current_mode_state->ctx.psr = 0xD3;	//Emulated SVC mode interrupts off

	addr_t start = curr_vm->config->firmware->vstart + curr_vm->config->guest_entry_offset;
#ifdef LINUX
	//Offset = 0x0001_0000 must be added since that offset is used to move the
	//guest by arm_guest_blob.S to 0x8100_0000 + 0x0001_0000, and pstart is also
	//set by arm_guest_blob.S.
	start = curr_vm->config->firmware->pstart + curr_vm->config->guest_entry_offset;
#endif

#if !defined(LINUX)
	__asm__ volatile ("mov LR, %0\n"
			  "mov r3, %1\n"
			  "mov r4, %2\n"
			  "mov r5, %3\n"
			  "mov r6, %4\n"
			  "MSR SPSR, #0xD0\n"
			  "MOVS PC, LR\n"::"r" (start), "r"(r3), "r"(r4),
			  "r"(r5), "r"(r6));
#else
	/*Prepare r0 r1 and r2 for linux boot */
	printf("Branching to address: %x\n", start);
	printf("Linux Arch ID: %x\n", LINUX_ARCH_ID);
	asm("mov LR, %0      \n\t"::"r"(start));
	__asm__ volatile ("mov lr, %0\n"
			  "mov r1, %1\n"
			  "mov r2, %2\n"
			  "mov r0, %3\n"
			  "MSR SPSR, #0xD0\n"
			  "MOVS PC, LR\n"::"r" (start), "r"(LINUX_ARCH_ID),
			  "r"(start - 0x10000 + 0x100), "r"(0));
#endif
}
