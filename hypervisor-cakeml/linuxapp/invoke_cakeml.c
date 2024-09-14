#include <stdio.h>
#include <stdint.h>
#include <string.h>	//For memcpy.
#include <unistd.h>

#define BUFFER_SIZE	10
#define cake_input_buffer_size	BUFFER_SIZE
#define cake_output_buffer_size	BUFFER_SIZE

int invoke_cake(uint32_t output_buffer, uint32_t output_buffer_size, uint32_t input_buffer, uint32_t input_buffer_size) {
	int result_code;
	uint32_t buffer_sizes = (output_buffer_size << 16) | input_buffer_size;
/*printf("invoke_cake: output_buffer = 0x%x\n", output_buffer);
printf("invoke_cake: output_buffer_size = 0x%x\n", output_buffer_size);
printf("invoke_cake: input_buffer = 0x%x\n", input_buffer);
printf("invoke_cake: input_buffer_size = 0x%x\n", input_buffer_size);*/
	asm volatile("mov r0, %0" : : "r" (output_buffer) : "r0");
	asm volatile("mov r1, %0" : : "r" (input_buffer) : "r1");
	asm volatile("mov r2, %0" : : "r" (buffer_sizes) : "r2");
	asm volatile("mov r7, #449" : : : "r7");		//Syscall number.
	asm volatile("svc 0x00000000" :::);				//System call.
	asm volatile("mov %0, r0" : "=r" (result_code) : :);	//Reads result code.

	return result_code;
}
