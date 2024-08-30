
    .extern handler_rpc
	.global _start

    .code 32
    .section .startup, "ax"
    .balign 4

	/*	The first 20 bytes constitute input and output buffers. It is up to the
		hypervisor and the cake ml guest to decide how to split this buffer into
		input and output. At the moment the input buffer is the first part and
		the output buffer is the second remaining part.
	 */
/*
	.word 0x0
	.word 0x1
	.word 0x2
	.word 0x3
	.word 0x4
*/
#define BUFFER_LENGTH 36864
#define CAKEML_INPUT_BUFFER_SZ	BUFFER_LENGTH
#define CAKEML_OUTPUT_BUFFER_SZ	BUFFER_LENGTH
#define BUFFER_SIZE				(CAKEML_INPUT_BUFFER_SZ + CAKEML_OUTPUT_BUFFER_SZ)
	.rept BUFFER_SIZE
	.byte 254
	.endr

    /* jump table */
_start:
	nop
	ldr r0, =__trusted_heap_start__;
	ldr r1, =__stack_bottom__;
	ldr r2, =__stack_top__;
    b handler_rpc
    nop
    nop
    nop
    nop
    nop
    nop

