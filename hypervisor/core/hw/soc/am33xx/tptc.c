////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
/////////New for Linux 5////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

#include <types.h>
#include <hyper.h>
extern virtual_machine *curr_vm;

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

#define is_word_aligned(address) ((address & 0x3) == 0)
#define is_sysconfig_tptc0_register_virtual_address(va) (va == TPTC0_VIRT + 0x10)
#define is_sysconfig_tptc1_register_virtual_address(va) (va == TPTC1_VIRT + 0x10)
#define is_sysconfig_tptc2_register_virtual_address(va) (va == TPTC2_VIRT + 0x10)

BOOL soc_check_tptc0_access(uint32_t accessed_va, uint32_t instruction_va) {
	uint32_t instruction_encoding = *((uint32_t *) instruction_va);
	uint32_t *context, t, n, imm, rt, rn;

	if (!is_word_aligned(accessed_va)) {
		printf("HYPERVISOR TPTC0: ACCESSED ADDRESS IS NOT WORD ALIGNED!");
		return FALSE;
	}

	switch (0xFFF00000 & instruction_encoding) {
		//STR  Rt, [Rn, #+imm32] = mem32[Regs[Rn] + imm32] := Regs[Rt]
	case 0xE5800000:

		t = (0x0000F000 & instruction_encoding) >> 12;
		n = (0x000F0000 & instruction_encoding) >> 16;
		imm = 0x00000FFF & instruction_encoding;

		context = curr_vm->current_mode_state->ctx.reg;
		rt = *(context + t);
		rn = *(context + n) + imm;

		if (rn != accessed_va) {
			printf("Hypervisor TPTC0 ERROR: Base register Regs[R%d] = %x distinct "
			       "from accessed address accessed_va = %x\n", n, rn, accessed_va);
			return FALSE;
		}

		if (is_sysconfig_tptc0_register_virtual_address(rn)) {
			*(( /*volatile */ uint32_t *) rn) = rt;
			return TRUE;
		}

		printf("TPTC0 ERROR: NOT REACHABLE CODE!\n");
		return FALSE;
		break;
	default:
		printf("TPTC0 ERROR: UNKNOWN INSTRUCTION TYPE WHEN ACCESSING TPTC0 REGISTER!\n");
		return FALSE;
		break;
	}

	printf("TPTC0 ERROR: UNREACHABLE POINT WAS REACHED IN HYPERVISOR TPTC0 DRIVER!\n");
	return FALSE;
}

BOOL soc_check_tptc1_access(uint32_t accessed_va, uint32_t instruction_va) {
	uint32_t instruction_encoding = *((uint32_t *) instruction_va);
	uint32_t *context, t, n, imm, rt, rn;

	if (!is_word_aligned(accessed_va)) {
		printf("HYPERVISOR TPTC1: ACCESSED ADDRESS IS NOT WORD ALIGNED!");
		return FALSE;
	}

	switch (0xFFF00000 & instruction_encoding) {
		//STR  Rt, [Rn, #+imm32] = mem32[Regs[Rn] + imm32] := Regs[Rt]
	case 0xE5800000:

		t = (0x0000F000 & instruction_encoding) >> 12;
		n = (0x000F0000 & instruction_encoding) >> 16;
		imm = 0x00000FFF & instruction_encoding;

		context = curr_vm->current_mode_state->ctx.reg;
		rt = *(context + t);
		rn = *(context + n) + imm;

		if (rn != accessed_va) {
			printf("Hypervisor TPTC1 ERROR: Base register Regs[R%d] = %x distinct "
			       "from accessed address accessed_va = %x\n", n, rn, accessed_va);
			return FALSE;
		}

		if (is_sysconfig_tptc1_register_virtual_address(rn)) {
			*(( /*volatile */ uint32_t *) rn) = rt;
			return TRUE;
		}

		printf("TPTC1 ERROR: NOT REACHABLE CODE!\n");
		return FALSE;
		break;
	default:
		printf("TPTC1 ERROR: UNKNOWN INSTRUCTION TYPE WHEN ACCESSING TPTC1 REGISTER!\n");
		return FALSE;
		break;
	}

	printf("TPTC1 ERROR: UNREACHABLE POINT WAS REACHED IN HYPERVISOR TPTC1 DRIVER!\n");
	return FALSE;
}

BOOL soc_check_tptc2_access(uint32_t accessed_va, uint32_t instruction_va) {
	uint32_t instruction_encoding = *((uint32_t *) instruction_va);
	uint32_t *context, t, n, imm, rt, rn;

	if (!is_word_aligned(accessed_va)) {
		printf("HYPERVISOR TPTC2: ACCESSED ADDRESS IS NOT WORD ALIGNED!");
		return FALSE;
	}

	switch (0xFFF00000 & instruction_encoding) {
		//STR  Rt, [Rn, #+imm32] = mem32[Regs[Rn] + imm32] := Regs[Rt]
	case 0xE5800000:
		t = (0x0000F000 & instruction_encoding) >> 12;
		n = (0x000F0000 & instruction_encoding) >> 16;
		imm = 0x00000FFF & instruction_encoding;

		context = curr_vm->current_mode_state->ctx.reg;
		rt = *(context + t);
		rn = *(context + n) + imm;

		if (rn != accessed_va) {
			printf("Hypervisor TPTC2 ERROR: Base register Regs[R%d] = %x distinct "
			       "from accessed address accessed_va = %x\n", n, rn, accessed_va);
			return FALSE;
		}

		if (is_sysconfig_tptc2_register_virtual_address(rn)) {
			*(( /*volatile */ uint32_t *) rn) = rt;
			return TRUE;
		}

		printf("TPTC2 ERROR: NOT REACHABLE CODE!\n");
		return FALSE;
		break;
	default:
		printf("TPTC2 ERROR: UNKNOWN INSTRUCTION TYPE WHEN ACCESSING TPTC2 REGISTER!\n");
		return FALSE;
		break;
	}

	printf("TPTC2 ERROR: UNREACHABLE POINT WAS REACHED IN HYPERVISOR TPTC2 DRIVER!\n");
	return FALSE;
}
