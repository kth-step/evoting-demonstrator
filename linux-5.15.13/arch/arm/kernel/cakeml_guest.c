#include <linux/syscalls.h>	//For SYSCALL_DEFINE1.
#include <asm/memory.h>		//For virt_to_phys.
#include <linux/slab.h>		//For kmalloc, kfree and GFP_KERNEL.

SYSCALL_DEFINE3(cakeml, uint32_t *, output_buffer, uint32_t *, input_buffer, uint32_t, buffer_sizes)
{
	long result_code = 0;
	uint32_t *kernel_output_buffer;
	uint32_t *kernel_input_buffer;
	uint32_t output_buffer_size = buffer_sizes >> 16;
	uint32_t input_buffer_size = 0x0000FFFF & buffer_sizes;

	//Allocates kernel memory for the update.
	kernel_output_buffer = (uint32_t *) kmalloc(output_buffer_size, GFP_KERNEL);
	if (kernel_output_buffer == NULL)
		return -1;

	kernel_input_buffer = (uint32_t *) kmalloc(input_buffer_size, GFP_KERNEL);
	if (kernel_input_buffer == NULL) {
		kfree((void *) kernel_output_buffer);
		return -2;
	}

	if (copy_from_user((void *) kernel_output_buffer, (void *) output_buffer, output_buffer_size) != 0) {
		kfree((void *) kernel_output_buffer);
		kfree((void *) kernel_input_buffer);
		return -3;
	}

	HYPERCALL_3(HYPERCALL_CAKEML, virt_to_phys(kernel_output_buffer), virt_to_phys(kernel_input_buffer), buffer_sizes)
	asm volatile("mov %0, r0" : "=r" (result_code) ::);	//Stores r0 in result_code.

	if (copy_to_user((void *) input_buffer, (void *) kernel_input_buffer, input_buffer_size) != 0) {
		kfree((void *) kernel_output_buffer);
		kfree((void *) kernel_input_buffer);
		return -4;
	}

	kfree((void *) kernel_output_buffer);
	kfree((void *) kernel_input_buffer);

	return result_code;
}
