#ifndef _HYPER_H_
#define _HYPER_H_

#include "hw.h"
#include "hypercalls.h"
#include "hyper_config_base.h"
#include "hyper_config.h"

#define MODE_NONE ((uint32_t)-1)	//Casts -1 to uint32_t = 0xFFFFFFFF.

typedef void (*interrupt_handler_fn) (void);
typedef void (*dabort_handler_fn) (void);
typedef void (*pabort_handler_fn) (void);

/*Data structures
 *
 * */

/*Boot information from guest that hypervisor needs*/

typedef struct guest_info_ {
	uint32_t *vector_table;
	uint32_t nr_syscalls;
	uint32_t page_offset;
	uint32_t phys_offset;
	addr_t vmalloc_end;
	uint32_t guest_size;
} guest_info;

typedef struct boot_info_ {
	guest_info guest;
	uint32_t cpu_id;
	uint32_t cpu_mmf;
	uint32_t cpu_cr;
} boot_info;

/*Virtual machine datastructures*/

typedef struct hyper_mode_state_ {
	context ctx;
	//Guest execution mode, including the domain access control bits that are
	//set when entering the mode.
	const struct hc_guest_mode_ *mode_config;
	uint32_t rpc_for;
	uint32_t rpc_to;
} hyper_mode_state;

typedef struct virtual_machine_ {
	uint32_t id;
	uint32_t current_guest_mode;
	uint32_t interrupted_mode;
	guest_info guest_info;
	uint32_t exception_vector[10];
	hyper_mode_state mode_states[HC_NGUESTMODES];	//HC_NGUESTMODES = 3.
	hyper_mode_state *current_mode_state;
	struct hc_config_ *config;
	struct virtual_machine_ *next;
} virtual_machine;

#endif
