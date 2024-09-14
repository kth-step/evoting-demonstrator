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
#include <unistd.h>
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

#define BUFFER_LENGTH 38960
#define TRUSTED_LOCATION 0xf0500000
// #define BUFFER_LENGTH 65000
// #define TRUSTED_LOCATION 0xF0A00000
#define CAKEML_INPUT_BUFFER_VA	TRUSTED_LOCATION
#define CAKEML_INPUT_BUFFER_SZ	BUFFER_LENGTH
#define CAKEML_OUTPUT_BUFFER_VA	(TRUSTED_LOCATION + CAKEML_INPUT_BUFFER_SZ)
#define CAKEML_OUTPUT_BUFFER_SZ	BUFFER_LENGTH

#ifdef EMULATE_HYPERVISOR
//char *cake_input_buffer;
//char *cake_output_buffer;
int cake_r;
int cake_w;
#endif

/*
#ifdef EMULATE_HYPERVISOR
void ffireceive_message_type(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
	cake_ml_buffer[0] = cake_input_buffer[0];
}
#else
void ffireceive_message_type(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
	char *input_buffer = (char *) 0xf0a00000;
	cake_ml_buffer[0] = input_buffer[0];
}
#endif
*/

#ifdef EMULATE_HYPERVISOR
void ffireceive_input_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
//  for (int i = 0; i < cake_ml_buffer_len && i < (BUFFER_LENGTH - 1); i++)
//    cake_ml_buffer[i] = cake_input_buffer[i];
	int min = cake_ml_buffer_len < BUFFER_LENGTH ? cake_ml_buffer_len : BUFFER_LENGTH;
	read(cake_r, cake_ml_buffer, min);
}
#else
void ffireceive_input_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
//	char *input_buffer = (char *) 0xf0a00000 + 1;
	char *input_buffer = (char *) CAKEML_INPUT_BUFFER_VA;

//	for (int i = 0; i < cake_ml_buffer_len && i < (BUFFER_LENGTH - 1); i++)
	for (int i = 0; i < cake_ml_buffer_len && i < CAKEML_INPUT_BUFFER_SZ; i++) {
		cake_ml_buffer[i] = input_buffer[i];
		// printf_("CakeML Input buffer byte %d: %c\n", cake_ml_buffer[i], cake_ml_buffer[i]);
	}
  printf_("CakeML receive input buffer len %d; bufstart", cake_ml_buffer_len);
  for (int i = 0; i < cake_ml_buffer_len && i < CAKEML_INPUT_BUFFER_SZ && i < 30; i++) {
    printf_(" %d", cake_ml_buffer[i]);
  }
  printf_("\n");
}
#endif

#ifdef EMULATE_HYPERVISOR
void ffisend_output_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
//	for (int i = 0; i < cake_ml_buffer_len && i < BUFFER_LENGTH; i++)
//		cake_output_buffer[i] = cake_ml_buffer[i];
	int min = cake_ml_buffer_len < BUFFER_LENGTH ? cake_ml_buffer_len : BUFFER_LENGTH;
	write(cake_w, cake_ml_buffer, min);
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
	unsigned char *output_buffer = (char *) CAKEML_OUTPUT_BUFFER_VA;

//  printf_("ffiwrite_output_buffer: trusted_buffer = %s\n", trusted_buffer);
//  printf_("ffiwrite_output_buffer: cake_ml_buffer_len = %d\n", cake_ml_buffer_len);

//  printf_("ffiwrite_output_buffer: cake_ml_buffer1 = ");
//  for (int i = 0; i < cake_ml_buffer_len; i++)
//    printf_("%c", cake_ml_buffer[i]);
//  printf_("\n");

//cake_ml_buffer_len = BUFFER_LENGTH;
	for (int i = 0; i < cake_ml_buffer_len && i < CAKEML_OUTPUT_BUFFER_SZ; i++)
		output_buffer[i] = cake_ml_buffer[i];
//  trusted_buffer[BUFFER_LENGTH - 1] = '\0';

//  printf_("ffiwrite_output_buffer: cake_ml_buffer2 = ");
//  for (int i = 0; i < cake_ml_buffer_len; i++)
//    printf_("%c", cake_ml_buffer[i]);
//  printf_("\n");
  printf_("CakeML send output buffer len %d; bufstart", cake_ml_buffer_len);
  for (int i = 0; i < cake_ml_buffer_len && i < CAKEML_INPUT_BUFFER_SZ && i < 30; i++) {
    printf_(" %d", cake_ml_buffer[i]);
  }
  printf_("\n");
  printf_("\n");
	ISSUE_HYPERCALL_REG1(HYPERCALL_END_RPC, CAKEML_OUTPUT_BUFFER_SZ);
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
void main(int local_argc, char **local_argv) {
	argc = local_argc;
	argv = local_argv;

	int cake_r0 = (int) *(local_argv[0]);
	int cake_r1 = ((int) *(local_argv[1])) << 8;
	int cake_r2 = ((int) *(local_argv[2])) << 16;
	int cake_r3 = ((int) *(local_argv[3])) << 24;
	cake_r = cake_r0 | cake_r1 | cake_r2 | cake_r3;

	int cake_w0 = (int) *(local_argv[4]);
	int cake_w1 = ((int) *(local_argv[5])) << 8;
	int cake_w2 = ((int) *(local_argv[6])) << 16;
	int cake_w3 = ((int) *(local_argv[7])) << 24;
	cake_w = cake_w0 | cake_w1 | cake_w2 | cake_w3;

//	printf("CakeML main: argc = %d\n", argc);
//	printf("CakeML main: cake_r0 = %d, cake_r1 = %d, cake_r2 = %d, cake_r3 = %d, cake_r = %d\n", cake_r0, cake_r1, cake_r2, cake_r3, cake_r);
//	printf("CakeML main: cake_w0 = %d, cake_w1 = %d, cake_w2 = %d, cake_w3 = %d, cake_w = %d\n", cake_w0, cake_w1, cake_w2, cake_w3, cake_w);

/*
	char tx = 'b', rx = 255;
	read(cake_r, &rx, 1);
	printf("CakeML received %c\n", rx);
	write(cake_w, &tx, 1);
	printf("CakeML has sent %c\n", tx);
*/
//	while (1);////////////////////////////////////////////////////////////////////////////////////////

	char *heap_env = getenv("CML_HEAP_SIZE");
	char *stack_env = getenv("CML_STACK_SIZE");
	char *temp; //used to store remainder of strtoul parse

	unsigned long sz = 1024*1024; // 1 MB unit
	unsigned long cml_heap_sz = 1024 * sz;    // Default: 1 GB heap
	unsigned long cml_stack_sz = 1024 * sz;   // Default: 1 GB stack

	// Read CML_HEAP_SIZE env variable (if present)
	// Warning: strtoul may overflow!
	if(heap_env != NULL) {
		cml_heap_sz = strtoul(heap_env, &temp, 10);
		cml_heap_sz *= sz; //heap size is read in units of MBs
	}

	if(stack_env != NULL) {
		cml_stack_sz = strtoul(stack_env, &temp, 10);
		cml_stack_sz *= sz; //stack size is read in units of MBs
	}

	if(cml_heap_sz < sz || cml_stack_sz < sz) { //At least 1MB heap and stack size
		fprintf(stderr,"Too small requested heap (%lu) or stack (%lu) size in bytes.\n",cml_heap_sz, cml_stack_sz);
		exit(3);
	}

	if(cml_heap_sz + cml_stack_sz < 8192) { // Global minimum heap/stack for CakeML. 4096 for 32-bit architectures
	    fprintf(stderr,"Too small requested heap (%lu) + stack (%lu) size in bytes.\n",cml_heap_sz, cml_stack_sz);
    	exit(3);
	}

	cml_heap = malloc(cml_heap_sz + cml_stack_sz); // allocate both heap and stack at once

	if(cml_heap == NULL) {
		fprintf(stderr,"failed to allocate sufficient CakeML heap and stack space.\n");
		perror("malloc");
		exit(3);
	}

	cml_stack = cml_heap + cml_heap_sz;
	cml_stackend = cml_stack + cml_stack_sz;

//	cake_input_buffer = malloc(BUFFER_LENGTH);
//	cake_output_buffer = malloc(BUFFER_LENGTH);

	cml_main(); // Passing control to CakeML
}
#else
void handler_rpc(void *heap, void *stack_bottom, void *stack_top) {
  cml_heap = heap;
  cml_stack = stack_bottom;
  cml_stackend = stack_top;
  cml_main(); // Passing control to CakeML
}
#endif
