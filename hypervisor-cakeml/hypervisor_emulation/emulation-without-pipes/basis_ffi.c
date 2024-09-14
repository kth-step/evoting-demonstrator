unsigned int argc;
char **argv;

/* exported in cake.S */
extern void cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

extern char cake_text_begin;
extern char cake_codebuffer_begin;
extern char cake_codebuffer_end;

#ifdef EMULATE_HYPERVISOR
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#define printf_	printf
//#define printf_(...)	printf(__VA_ARGS__)
#else
//For printing in print.c.
extern void printf_(const char *fmt, ...);
#endif

/* Signal handler for SIGINT */
void ffipoll_sigint (unsigned char *c, long clen, unsigned char *a, long alen) { }

void ffikernel_ffi (unsigned char *c, long clen, unsigned char *a, long alen) { }

void ffiget_arg_count (unsigned char *c, long clen, unsigned char *a, long alen) {
  a[0] = (char) argc;
  a[1] = (char) (argc / 256);
}

void ffiget_arg_length (unsigned char *c, long clen, unsigned char *a, long alen) {
  int i = a[0] + (a[1] * 256);
  int k = 0;
  while (argv[i][k] != 0) { k++; }
  a[0] = (char) k;
  a[1] = (char) (k / 256);
}

void ffiget_arg (unsigned char *c, long clen, unsigned char *a, long alen) {
  int i = a[0] + (a[1] * 256);
  int k = 0;
  while (argv[i][k] != 0) {
    a[k] = argv[i][k];
    k++;
  }
}

void int_to_byte2(int i, unsigned char *b){
    /* i is encoded on 2 bytes */
    b[0] = (i >> 8) & 0xFF;
    b[1] = i & 0xFF;
}

int byte2_to_int(unsigned char *b){
    return ((b[0] << 8) | b[1]);
}

void int_to_byte8(int i, unsigned char *b){
    /* i is encoded on 8 bytes */
    /* i is cast to long long to ensure having 64 bits */
    /* assumes CHAR_BIT = 8. use static assertion checks? */
    b[0] = ((long long) i >> 56) & 0xFF;
    b[1] = ((long long) i >> 48) & 0xFF;
    b[2] = ((long long) i >> 40) & 0xFF;
    b[3] = ((long long) i >> 32) & 0xFF;
    b[4] = ((long long) i >> 24) & 0xFF;
    b[5] = ((long long) i >> 16) & 0xFF;
    b[6] = ((long long) i >> 8) & 0xFF;
    b[7] =  (long long) i & 0xFF;
}

int byte8_to_int(unsigned char *b){
    return (((long long) b[0] << 56) | ((long long) b[1] << 48) |
             ((long long) b[2] << 40) | ((long long) b[3] << 32) |
             (b[4] << 24) | (b[5] << 16) | (b[6] << 8) | b[7]);
}

void ffiopen_in (unsigned char *c, long clen, unsigned char *a, long alen) {
/*
  assert(9 <= alen);
  int fd = open((const char *) c, O_RDONLY);
  if (0 <= fd){
    a[0] = 0;
    int_to_byte8(fd, &a[1]);
  }
  else
    a[0] = 1;
*/
}

void ffiopen_out (unsigned char *c, long clen, unsigned char *a, long alen) {
/*
  assert(9 <= alen);
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC);
  if (0 <= fd){
    a[0] = 0;
    int_to_byte8(fd, &a[1]);
  }
  else
    a[0] = 1;
*/
}

void ffiread (unsigned char *c, long clen, unsigned char *a, long alen) {
/*
  assert(clen == 8);
  int fd = byte8_to_int(c);
  int n = byte2_to_int(a);
  assert(alen >= n + 4);
  int nread = read(fd, &a[4], n);
  if(nread < 0){
    a[0] = 1;
  }
  else{
    a[0] = 0;
    int_to_byte2(nread,&a[1]);
  }
*/
}

void ffiwrite (unsigned char *c, long clen, unsigned char *a, long alen){

//  assert(clen == 8);
  int fd = byte8_to_int(c);
  int n = byte2_to_int(a);
  int off = byte2_to_int(&a[2]);
//  assert(alen >= n + off + 4);
//  printf_("CakeML: ");
  printf_(&a[4 + off]);
/*
  int nw = write(fd, &a[4 + off], n);
  if(nw < 0){
      a[0] = 1;
  }
  else{
    a[0] = 0;
    int_to_byte2(nw,&a[1]);
  }
*/
}

void fficlose (unsigned char *c, long clen, unsigned char *a, long alen) {
/*
  assert(alen >= 1);
  assert(clen == 8);
  int fd = byte8_to_int(c);
  if (close(fd) == 0) a[0] = 0;
  else a[0] = 1;
*/
}

void ffiexit (unsigned char *c, long clen, unsigned char *a, long alen) {
//  assert(alen == 1);
//  exit((int)a[0]);
}


/* empty FFI (assumed to do nothing, but can be used for tracing/logging) */
void ffi (unsigned char *c, long clen, unsigned char *a, long alen) {

}

typedef union {
  double d;
  char bytes[8];
} double_bytes;

// FFI calls for floating-point parsing
void ffidouble_fromString (char *c, long clen, char *a, long alen) {
  double_bytes d;
//  sscanf(c, "%lf",&d.d);
//  assert (8 == alen);
  for (int i = 0; i < 8; i++){
    a[i] = d.bytes[i];
  }
}

void ffidouble_toString (char *c, long clen, char *a, long alen) {
  double_bytes d;
//  assert (256 == alen);
  for (int i = 0; i < 8; i++){
    d.bytes[i] = a[i];
  }
  //snprintf always terminates with a 0 byte if space was sufficient
//  int bytes_written = snprintf(&a[0], 255, "%.20g", d.d);
  // snprintf returns number of bytes it would have written if the buffer was
  // large enough -> check that it did not write more than the buffer size - 1
  // for the 0 byte
//  assert (bytes_written <= 255);
}

void cml_clear() {
  __builtin___clear_cache(&cake_codebuffer_begin, &cake_codebuffer_end);
}

#define BUFFER_LENGTH 65000

#ifdef EMULATE_HYPERVISOR
extern char *cake_input_buffer;
extern char *cake_output_buffer;
#endif

#ifdef EMULATE_HYPERVISOR
void ffireceive_message_type(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
printf_("ffireceive_message_type1\n");
  cake_ml_buffer[0] = 0;//cake_input_buffer[0];
printf_("ffireceive_message_type2\n");
}
#else
void ffireceive_message_type(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
  char *input_buffer = (char *) 0xf0a00000;
  cake_ml_buffer[0] = input_buffer[0];
}
#endif

#ifdef EMULATE_HYPERVISOR
void ffireceive_input_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
  for (int i = 0; i < cake_ml_buffer_len && i < (BUFFER_LENGTH - 1); i++)
    cake_ml_buffer[i] = 0;//cake_input_buffer[i];
}
#else
void ffireceive_input_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
  char *input_buffer = (char *) 0xf0a00000 + 1;

  for (int i = 0; i < cake_ml_buffer_len && i < (BUFFER_LENGTH - 1); i++)
    cake_ml_buffer[i] = input_buffer[i];
}
#endif

#ifdef EMULATE_HYPERVISOR
uint64_t rbx;
uint64_t r12;
uint64_t r13;
uint64_t r14;
uint64_t r15;
uint64_t rflags;

extern void cakeml_to_rust(uint64_t);

uint64_t cake2rust(uint64_t rust_address) {
	cakeml_to_rust(rust_address);
	asm volatile("movq %%rdi, %0" : "=r" (rust_address) : :);
	return rust_address;
}

uint64_t rust_address;

void ffisend_output_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
printf("ffisend_output_buffer1\n");
	for (int i = 0; i < cake_ml_buffer_len && i < BUFFER_LENGTH; i++)
		cake_output_buffer[i] = cake_ml_buffer[i];
printf("ffisend_output_buffer2\n");
	//Store registers.
	asm volatile("movq %%rbx, %0" : "=r"(rbx) : :);		//Store rbx.
	asm volatile("movq %%r12, %0" : "=r"(r12) : :);
	asm volatile("movq %%r13, %0" : "=r"(r13) : :);
	asm volatile("movq %%r14, %0" : "=r"(r14) : :);
	asm volatile("movq %%r15, %0" : "=r"(r15) : :);
	asm volatile("pushfq" : : :);						//Push RFLAGS onto stack.
	asm volatile("popq %%r15" : : :);						//Pop flags in r15, that has been saved.
	asm volatile("movq %%r15, %0" : "=r"(rflags) : :);	//Store flags in flags variable.
printf("ffisend_output_buffer3\n");
	rust_address = cake2rust(rust_address);
printf("ffisend_output_buffer4\n");
	//Restore registers.
	asm volatile("movq %0, %%r15" : : "r" (rflags) :);	//Save flags in r15.
	asm volatile("pushq %%r15" : : :);					//Push flags onto stack.
	asm volatile("popfq" : : :);						//Pop flags from stack into RFLAGS.
	asm volatile("movq %0, %%r15" : : "r" (r15));
	asm volatile("movq %0, %%r14" : : "r" (r14));
	asm volatile("movq %0, %%r13" : : "r" (r13));
	asm volatile("movq %0, %%r12" : : "r" (r12));
	asm volatile("movq %0, %%rbx" : : "r" (rbx));
}
#else

#define HYPERCALL_END_RPC				1021
#define STR(x) #x
#define HYPERCALL_NUM(n) "#"STR(n)
#define ISSUE_HYPERCALL_REG1(num, reg0)			   \
  asm volatile ("mov R0, %0 			\n\t"  	   \
		"SWI " HYPERCALL_NUM((num)) "\n\t"	       \
		::"r" (reg0) : "memory", "r0"		       \
		);

void ffisend_output_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
  unsigned char *output_buffer = (char *) (0xf0a00000 + 10);

//  printf_("ffiwrite_output_buffer: trusted_buffer = %s\n", trusted_buffer);
//  printf_("ffiwrite_output_buffer: cake_ml_buffer_len = %d\n", cake_ml_buffer_len);

//  printf_("ffiwrite_output_buffer: cake_ml_buffer1 = ");
//  for (int i = 0; i < cake_ml_buffer_len; i++)
//    printf_("%c", cake_ml_buffer[i]);
//  printf_("\n");

//cake_ml_buffer_len = BUFFER_LENGTH;
  for (int i = 0; i < cake_ml_buffer_len && i < BUFFER_LENGTH; i++)
    output_buffer[i] = cake_ml_buffer[i];
//  trusted_buffer[BUFFER_LENGTH - 1] = '\0';

//  printf_("ffiwrite_output_buffer: cake_ml_buffer2 = ");
//  for (int i = 0; i < cake_ml_buffer_len; i++)
//    printf_("%c", cake_ml_buffer[i]);
//  printf_("\n");
  ISSUE_HYPERCALL_REG1(HYPERCALL_END_RPC, BUFFER_LENGTH);
}
#endif

void cml_exit(int arg) {
	printf_("cml_exit: Infinite while\n");
	while (1);
}

void ffiprintf(unsigned char *c, long clen, unsigned char *string, long string_len) {
	for (int i = 0; i < string_len; i++)
		printf_("%c", string[i]);
}

#ifdef EMULATE_HYPERVISOR
extern uint64_t cakeml_sp;
extern uint64_t cakeml_bp;

void initialize_cake(void *heap, void *stack_bottom, void *stack_top, char *cakeml_input, char *cakeml_output) {
	cml_heap = malloc(10*1024*1024); //5 MB heap + 5 MB stack.

	if(cml_heap == NULL) {
		printf("initialize_cake: No heap!\n");
		while (1);
	}

	cml_stack = cml_heap + 5*1024*1024;
	cml_stackend = cml_stack + 5*1024*1024;
///////////////


//	cml_heap = heap;
//	cml_stack = stack_bottom;
//	cml_stackend = stack_top;
	cake_input_buffer = cakeml_input;
	cake_output_buffer = cakeml_output;

//	cakeml_sp = (uint64_t) stack_top;	//Old before testing.
	cakeml_sp = (uint64_t) cml_stackend;
//	cakeml_bp = rbp;
}

void cakeml(void *rust_return_address) {
	rust_address = (uint64_t) rust_return_address;

printf_("cakeml: cakeml_sp: 0x%lX\n", cakeml_sp);
printf_("cakeml: cakeml_bp: 0x%lX\n", cakeml_bp);

	uint64_t sp, bp;
	asm volatile("movq %%rsp, %0" : "=r"(sp) : :);
	asm volatile("movq %%rbp, %0" : "=r"(bp) : :);
printf_("cakeml: sp: 0x%lX\n", sp);
printf_("cakeml: bp: 0x%lX\n", bp);
printf_("cakeml!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");

	cml_main();
}
#else
void handler_rpc(void *heap, void *stack_bottom, void *stack_top) {
  cml_heap = heap;
  cml_stack = stack_bottom;
  cml_stackend = stack_top;
  cml_main(); // Passing control to CakeML
}
#endif
