#include "hw.h"
#include "hyper_config.h"
#include "hyper.h"

extern virtual_machine *curr_vm;

void hypercall_rpc(void) {
	const hc_rpc_handler *handler = curr_vm->config->rpc_handlers;
	uint32_t handling_mode = handler->mode;

	if (curr_vm->current_mode_state->rpc_to != MODE_NONE)
		hyper_panic("Guest trying to start RPC while being in one", 1);

	if (curr_vm->current_guest_mode == handling_mode)
		hyper_panic("Guest trying to send RPC to itself", 1);

	if (curr_vm->mode_states[handling_mode].rpc_for != MODE_NONE)
		hyper_panic("Guest trying to send RPC to a mode that is already handling a RPC", 1);

	curr_vm->current_mode_state->rpc_to = handling_mode;
	curr_vm->mode_states[handling_mode].rpc_for = curr_vm->current_guest_mode;
	change_guest_mode(HC_GM_TRUSTED);
//	curr_vm->current_mode_state->ctx.reg[0] = rpc_op;	//Not needed for CCTV.
//printf("hyperivosr/core/hypervisor/hypercalls/hyp_rpc.c:hypercall_rpc: curr_vm->current_mode_state->ctx.pc = 0x%x\n", curr_vm->current_mode_state->ctx.pc);
//printf("hyperivosr/core/hypervisor/hypercalls/hyp_rpc.c:hypercall_rpc: memory[curr_vm->current_mode_state->ctx.pc] = 0x%x\n", *((uint32_t *) curr_vm->current_mode_state->ctx.pc));
//	curr_vm->current_mode_state->ctx.pc = handler->entry_point;
	curr_vm->current_mode_state->ctx.sp = curr_vm->config->rpc_handlers->sp;
	curr_vm->current_mode_state->ctx.psr = 0xD0;	/*USR mode, IRQ off */
}

void hypercall_end_rpc(uint32_t result) {
	uint32_t calling_mode = curr_vm->current_mode_state->rpc_for;

//NEW
//	curr_vm->current_mode_state->ctx.pc += 4;
//END OF NEW


	if (calling_mode == MODE_NONE)
		hyper_panic("Guest ended rpc without being in one", 1);

	if (curr_vm->mode_states[calling_mode].rpc_to != curr_vm->current_guest_mode)
		hyper_panic("Guest trying to end rpc but caller did not start one", 1);

	calling_mode = curr_vm->current_mode_state->rpc_for;

	curr_vm->current_mode_state->rpc_for = MODE_NONE;
	curr_vm->mode_states[calling_mode].rpc_to = MODE_NONE;

	change_guest_mode(calling_mode);

	curr_vm->current_mode_state->ctx.reg[0] = result;
}
