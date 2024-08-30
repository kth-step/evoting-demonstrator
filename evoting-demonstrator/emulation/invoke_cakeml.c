#include <stdint.h>

#define BUFFER_SIZE	38960
#define cake_input_buffer_size	BUFFER_SIZE
#define cake_output_buffer_size	BUFFER_SIZE

#ifdef EMULATE_HYPERVISOR
#include <stdio.h>
#include <string.h>	//For memcpy.
#include <unistd.h>
#include <stdbool.h>	//For true/false.

unsigned char pipe_buffer[BUFFER_SIZE];

void invoke_cake(uint64_t rust_output_buffer, uint64_t rust_output_buffer_size, uint64_t rust_input_buffer, uint64_t rust_input_buffer_size_ptr, uint64_t rust_read, uint64_t rust_write) {
//	char tx = 'a', rx = 255;
	int min_out = rust_output_buffer_size < BUFFER_SIZE ? rust_output_buffer_size : BUFFER_SIZE;
	uint64_t *rust_input_buffer_size = (uint64_t *) rust_input_buffer_size_ptr;
	int min_in = *rust_input_buffer_size < BUFFER_SIZE ? *rust_input_buffer_size : BUFFER_SIZE;

  	printf("[c invoke_cake] Emulated hypervisor: rust_read = %lu, rust_write = %lu\n", rust_read, rust_write);
  	printf("[c invoke_cake] rust_input_buffer = 0x%llx\n", rust_input_buffer);
  	printf("[c invoke_cake] rust_input_buffer_size = %lld\n", *rust_input_buffer_size);
  	printf("[c invoke_cake] min_in buffer length: %d\n", min_in);
  	printf("[c invoke_cake] rust_output_buffer = 0x%llx\n", rust_output_buffer);
  	printf("[c invoke_cake] rust_output_buffer_size = %lld\n", rust_output_buffer_size);
  	printf("[c invoke_cake] min_out buffer length: %d\n", min_out);

//	printf("invoke_cake sends %c\n", tx);
    int min_out_print = min_out < 30 ? min_out : 30;
    int min_in_print = min_in < 30 ? min_in : 30;
//*
    printf("[c invoke_cake] rust_output_buffer (first %d):", min_out_print);
    unsigned char * out_ptr = (unsigned char *) rust_output_buffer;
	for (int i = 0; i < min_out_print; i++) {
	  printf(" %x", out_ptr[i]);
    }
    printf("\n");
    printf("[c invoke_cake] rust_input_buffer (first %d):", min_in_print);
    unsigned char * in_ptr = (unsigned char *) rust_input_buffer;
	for (int i = 0; i < min_in_print; i++) {
	  printf(" %x", in_ptr[i]);
    }
// */
    // write(int fd, const void buf, size_t count)
    printf("\n");
    printf("[c invoke_cake] write(rust_write=%d, (const void *) rust_output_buffer, min_out=%d)\n", rust_write, min_out);

	// write(rust_write, (const void *) rust_output_buffer, min_out);
    memcpy(pipe_buffer, (void *) rust_output_buffer, min_out);
    write(rust_write, pipe_buffer, BUFFER_SIZE);

//	memcpy((void *) cake_input_buffer, (const void *) rust_output_buffer, rust_output_buffer_size);	//(dest, src, size).
//	printf("invoke_cake waits for data\n");

    printf("[c invoke_cake] wait for calculation of CakeML\n");
    if (min_in <= 0) {
      printf("[c invoke_cake] cannot read into empty rust_input_buffer.\n");
    }
    printf("[c invoke_cake] read(rust_read=%d, (void *) rust_input_buffer, min_in=%d)\n", rust_read, min_in);


	// int n = read(rust_read, (void *) rust_input_buffer, min_in);
    int n = 0;
    while (n < BUFFER_SIZE) {
      n += read(rust_read, pipe_buffer + n, BUFFER_SIZE - n);
    }

    for (int i = 0; i < min_in; i++)
        ((unsigned char *) rust_input_buffer)[i] = pipe_buffer[i];


    printf("[c invoke_cake] receive %d bytes from rust_read pipe\n", n);

    if (0 <= n) {
      min_in_print = n < 30 ? n : 30;
      printf("[c invoke_cake] rust_input_buffer (first %d):", min_in_print);
      for (int i = 0; i < min_in_print; i++) {
        printf(" %x", in_ptr[i]);
      }
      printf("\n");
    }

    if (n < 0) {
      #include <errno.h>
      switch (errno) {
        case EAGAIN:
          printf("error EAGAIN|EWOULDBLOCK - fd refers to a socket and has been marked nonblocking\n"); break;
        case EBADF:
          printf("error EBADF\n"); break;
        case EFAULT:
          printf("error EFAULT - buffer is outside accessible address space\n"); break;
        case EINTR:
          printf("error EINTR\n"); break;
        case EINVAL:
          printf("error EINVAL\n"); break;
        case EIO:
          printf("error EIO\n"); break;
        case EISDIR:
          printf("error EISDIR\n"); break;
        default:
          printf("error implementation defined (default)\n");
      }
      printf("[c invoke_cake] no read from rust pipe\n");
    }
}
#else
void invoke_cake(uint32_t output_buffer, uint32_t output_buffer_size, uint32_t input_buffer, uint32_t input_buffer_size) {
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
}
#endif

