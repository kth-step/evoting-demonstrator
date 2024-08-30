#ifdef EMULATE_HYPERVISOR
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <assert.h>
#endif

unsigned int argc;
char **argv;

/* exported in cake.S */
extern void cml_main(void);
extern char *cml_heap;
extern char *cml_stack;
extern char *cml_stackend;

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


/* fsFFI (file system and I/O) */

void ffiopen_in (unsigned char *c, long clen, unsigned char *a, long alen) {
#ifdef EMULATE_HYPERVISOR
  assert(9 <= alen);
  int fd = open((const char *) c, O_RDONLY);
  if (0 <= fd){
    a[0] = 0;
    int_to_byte8(fd, &a[1]);
  }
  else
    a[0] = 1;
#endif
}

void ffiopen_out (unsigned char *c, long clen, unsigned char *a, long alen) {
#ifdef EMULATE_HYPERVISOR
  assert(9 <= alen);
  #ifdef __WIN32
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC);
  #else
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH);
  #endif
  if (0 <= fd){
    a[0] = 0;
    int_to_byte8(fd, &a[1]);
  }
  else
    a[0] = 1;
#endif
}

void ffiread (unsigned char *c, long clen, unsigned char *a, long alen) {
#ifdef EMULATE_HYPERVISOR
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
#endif
}

void ffiwrite (unsigned char *c, long clen, unsigned char *a, long alen){
//  assert(clen == 8);
  int fd = byte8_to_int(c);
  int n = byte2_to_int(a);
  int off = byte2_to_int(&a[2]);
#ifndef EMULATE_HYPERVISOR
  printf_("CakeML: \n");
  printf_(&a[4 + off]);
#endif
#ifdef EMULATE_HYPERVISOR
  assert(clen == 8);
  assert(alen >= n + off + 4);
  int nw = write(fd, &a[4 + off], n);
  if(nw < 0){
      a[0] = 1;
  }
  else{
    a[0] = 0;
    int_to_byte2(nw,&a[1]);
  }
#endif
}

void fficlose (unsigned char *c, long clen, unsigned char *a, long alen) {
#ifdef EMULATE_HYPERVISOR
  assert(alen >= 1);
  assert(clen == 8);
  int fd = byte8_to_int(c);
  if (close(fd) == 0) a[0] = 0;
  else a[0] = 1;
#endif
}

void ffiexit (unsigned char *c, long clen, unsigned char *a, long alen) {
  printf_("exit()\n");
//  assert(alen == 1);
//  exit((int)a[0]);
}


/* empty FFI (assumed to do nothing, but can be used for tracing/logging) */
void ffi (unsigned char *c, long clen, unsigned char *a, long alen) {
#ifdef EMULATE_HYPERVISOR
  #ifdef DEBUG_FFI
  {
    if (clen == 0)
    {
      if(inGC==1)
      {
        gettimeofday(&t2, NULL);
        microsecs += (t2.tv_usec - t1.tv_usec) + (t2.tv_sec - t1.tv_sec)*1e6;
        numGC++;
        inGC = 0;
      }
      else
      {
        inGC = 1;
        gettimeofday(&t1, NULL);
      }
    } else {
      int indent = 30;
      for (int i=0; i<clen; i++) {
        putc(c[i],stderr);
        indent--;
      }
      for (int i=0; i<indent; i++) {
        putc(' ',stderr);
      }
      struct timeval nowT;
      gettimeofday(&nowT, NULL);
      if (hasT) {
        long usecs = (nowT.tv_usec - lastT.tv_usec) +
                     (nowT.tv_sec - lastT.tv_sec)*1e6;
        fprintf(stderr," --- %ld milliseconds\n",usecs / (long)1000);
      } else {
        fprintf(stderr,"\n");
      }
      gettimeofday(&lastT, NULL);
      hasT = 1;
    }
  }
  #endif
#endif
}

typedef union {
  double d;
  char bytes[8];
} double_bytes;

// FFI calls for floating-point parsing
void ffidouble_fromString (char *c, long clen, char *a, long alen) {
#ifdef EMULATE_HYPERVISOR
  double_bytes d;
  sscanf(c, "%lf",&d.d);
  assert (8 == alen);
  for (int i = 0; i < 8; i++){
    a[i] = d.bytes[i];
  }
#endif
}

void ffidouble_toString (char *c, long clen, char *a, long alen) {
#ifdef EMULATE_HYPERVISOR
  double_bytes d;
  assert (256 == alen);
  for (int i = 0; i < 8; i++){
    d.bytes[i] = a[i];
  }
  //snprintf always terminates with a 0 byte if space was sufficient
  int bytes_written = snprintf(&a[0], 255, "%.20g", d.d);
  // snprintf returns number of bytes it would have written if the buffer was
  // large enough -> check that it did not write more than the buffer size - 1
  // for the 0 byte
  assert (bytes_written <= 255);
#endif
}

void cml_clear() {
#ifdef __GNUC__
  __builtin___clear_cache(&cake_codebuffer_begin, &cake_codebuffer_end);
#endif
}

#define BUFFER_LENGTH 38960
#define TRUSTED_LOCATION 0xF0500000
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
unsigned char pipe_buffer[BUFFER_LENGTH];

void _ffireceive_input_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
  printf_("[c _ffireceive_input_buffer] enter; wait for read\n");
//  for (int i = 0; i < cake_ml_buffer_len && i < (BUFFER_LENGTH - 1); i++)
//    cake_ml_buffer[i] = cake_input_buffer[i];
  int min = cake_ml_buffer_len < BUFFER_LENGTH ? cake_ml_buffer_len : BUFFER_LENGTH;
  int min_print = min < 30 ? min : 30;
  // read from cake_r to cake_ml_buffer
  printf_("[c _ffireceive_input_buffer] read(cake_r=%d, cake_ml_buffer, min=%d)\n", cake_r, min);

  int n = 0;
  while (n < BUFFER_LENGTH) {
    n += read(cake_r, pipe_buffer + n, BUFFER_LENGTH - n);
    if (n == 0) {
      printf_("[c _ffireceive_input_buffer] stopping read, received 0\n");
      break;
    }
  }

  for (int i = 0; i < min; i++)
      cake_ml_buffer[i] = pipe_buffer[i];

  printf_("[c _ffireceive_input_buffer] receive %d bytes from cake_r pipe\n", n);

  if (n < 0) {
    #include <errno.h>
    switch (errno) {
      case EAGAIN:
        printf_("error EAGAIN|EWOULDBLOCK - fd refers to a socket and has been marked nonblocking\n"); break;
      case EBADF:
        printf_("error EBADF\n"); break;
      case EFAULT:
        printf_("error EFAULT - buffer is outside accessible address space\n"); break;
      case EINTR:
        printf_("error EINTR\n"); break;
      case EINVAL:
        printf_("error EINVAL\n"); break;
      case EIO:
        printf_("error EIO\n"); break;
      case EISDIR:
        printf_("error EISDIR\n"); break;
      default:
        printf_("error implementation defined (default)\n");
    }
    printf_("[c _ffireceive_input_buffer] no read from rust pipe\n");
  }

  printf_("[c _ffireceive_input_buffer] data in cake_ml_buffer (after read) (%d bytes): ", min);
  for (int i = 0; i < min_print; i++) {
    printf_("%x ", cake_ml_buffer[i]);
  }
  printf_("\n");
  printf_("[c _ffireceive_input_buffer] return\n", min);
}
#else
void _ffireceive_input_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
//	char *input_buffer = (char *) 0xf0a00000 + 1;
	char *input_buffer = (char *) CAKEML_INPUT_BUFFER_VA;

	int min = cake_ml_buffer_len < BUFFER_LENGTH ? cake_ml_buffer_len : BUFFER_LENGTH;
	for (int i = 0; i < min; i++)
		cake_ml_buffer[i] = input_buffer[i];
}
#endif

#ifdef EMULATE_HYPERVISOR
unsigned char pipe_buffer_send[BUFFER_LENGTH];

void _ffisend_output_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
  printf_("[c _ffisend_output_buffer] enter\n");
	int min = cake_ml_buffer_len < BUFFER_LENGTH ? cake_ml_buffer_len : BUFFER_LENGTH;
    // max length of data is encoded in the header (2 bytes)
    // int data_head_len = byte2_to_int(cake_ml_buffer) + 2;
  printf_("[c _ffisend_output_buffer] data len: (%d bytes): [", cake_ml_buffer_len);
    // min = min < data_head_len ? min : data_head_len;
    int max_print = 60;
    int min_print = min < max_print ? min : max_print;
  for (int i = 0; i < min_print; i++) {
    printf_(" %d;", cake_ml_buffer[i]);
  }
  printf_("]\n");
  //printf_("[c _ffisend_output_buffer] data to write to fd: %d bytes\n", min);
  // write buffer cake_ml_buffer to file descriptor cake_w
  printf_("[c _ffisend_output_buffer] write(cake_w=%d, cake_ml_buffer, min=%d)\n", cake_w, min);

  memcpy(pipe_buffer_send, cake_ml_buffer, min);
  write(cake_w, pipe_buffer_send, BUFFER_LENGTH);

  printf_("[c _ffisend_output_buffer] data written to fd (%d bytes): [", min);
  for (int i = 0; i < min_print; i++) {
    printf_(" %d;", cake_ml_buffer[i]);
  }
  printf_("]\n");
  printf_("[c _ffisend_output_buffer] return\n");
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

void _ffisend_output_buffer(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
	unsigned char *output_buffer = (char *) CAKEML_OUTPUT_BUFFER_VA;
    int min = cake_ml_buffer_len < CAKEML_OUTPUT_BUFFER_SZ ? cake_ml_buffer_len : CAKEML_OUTPUT_BUFFER_SZ;

//  printf_("ffiwrite_output_buffer: trusted_buffer = %s\n", trusted_buffer);
//  printf_("ffiwrite_output_buffer: cake_ml_buffer_len = %d\n", cake_ml_buffer_len);

//  printf_("ffiwrite_output_buffer: cake_ml_buffer1 = ");
//  for (int i = 0; i < cake_ml_buffer_len; i++)
//    printf_("%c", cake_ml_buffer[i]);
//  printf_("\n");

//cake_ml_buffer_len = BUFFER_LENGTH;
	for (int i = 0; i < min; i++)
		output_buffer[i] = cake_ml_buffer[i];
//  trusted_buffer[BUFFER_LENGTH - 1] = '\0';

//  printf_("ffiwrite_output_buffer: cake_ml_buffer2 = ");
//  for (int i = 0; i < cake_ml_buffer_len; i++)
//    printf_("%c", cake_ml_buffer[i]);
//  printf_("\n");
	ISSUE_HYPERCALL_REG1(HYPERCALL_END_RPC, CAKEML_OUTPUT_BUFFER_SZ);
}
#endif

// put_get combines sending (put) and receiving (get)
void ffiput_get(unsigned char *c, long clen, unsigned char *cake_ml_buffer, long cake_ml_buffer_len) {
  printf_("[c ffiput_get] start\n");
  int min = cake_ml_buffer_len < BUFFER_LENGTH ? cake_ml_buffer_len : BUFFER_LENGTH;
  printf_("[c ffiput_get] min %d, cake_ml_buffer_len %d\n", min, cake_ml_buffer_len);
  // output is in cake_ml_buffer
  printf_("[c ffiput_get] call to _ffisend_output_buffer\n");
  _ffisend_output_buffer(c, clen, cake_ml_buffer, cake_ml_buffer_len);
  printf_("[c ffiput_get] return from _ffisend_output_buffer\n");
  // input gets put into
  printf_("[c ffiput_get] call to _ffireceive_input_buffer\n");
  _ffireceive_input_buffer(c, clen, cake_ml_buffer, cake_ml_buffer_len);
  printf_("[c ffiput_get] return from _ffireceive_input_buffer\n");
//  printf_("\n");
//  min = 50;
//  for (int i = 0; i < min; i++) {
//    printf_("%x ", cake_ml_buffer[i]);
//  }
//  printf_("\n");
  printf_("[c ffiput_get] end\n");
}

void ffiget_self (unsigned char *c, long clen, unsigned char *a, long alen) {
  printf_("[c ffiget_self] clen %d, alen %d\n", clen, alen);

#ifdef EMULATE_HYPERVISOR
  char path[256];
  if (getcwd(path, sizeof(path)) == NULL) {
    perror("error executing getcwd()");
  }
  printf_("[c ffiget_self] the current working directory is: %s\n", path);

  assert(0 < alen);
#endif
  //printf_("before: \n");
  // for(int i = 0; i < alen; i++)
  //   printf_("%x ", a[i]);
  // printf_("\n");
  printf_("[c ffiget_self] call to _ffireceive_input_buffer\n");
  _ffireceive_input_buffer(c, clen, a, alen);
  printf_("[c ffiget_self] return from _ffireceive_input_buffer\n");
  // printf_("after: \n");
  // for(int i = 0; i < alen; i++)
  //   printf_("%x ", a[i]);
  // printf_("\n");
  printf_("[c ffiget_self] end\n");
}

void cml_exit(int arg) {
	printf_("cml_exit: Infinite while\n");
	while (1);
}

void ffiprintf(unsigned char *c, long clen, unsigned char *string, long string_len) {
  // printf_("call to ffiprintf ");
	for (int i = 0; i < string_len; i++)
		printf_("%c", string[i]);
}

#ifdef EMULATE_HYPERVISOR
int main(int local_argc, char **local_argv) {
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

//	printf_("CakeML main: argc = %d\n", argc);
//	printf_("CakeML main: cake_r0 = %d, cake_r1 = %d, cake_r2 = %d, cake_r3 = %d, cake_r = %d\n", cake_r0, cake_r1, cake_r2, cake_r3, cake_r);
//	printf_("CakeML main: cake_w0 = %d, cake_w1 = %d, cake_w2 = %d, cake_w3 = %d, cake_w = %d\n", cake_w0, cake_w1, cake_w2, cake_w3, cake_w);

/*
	char tx = 'b', rx = 255;
	read(cake_r, &rx, 1);
	printf_("CakeML received %c\n", rx);
	write(cake_w, &tx, 1);
	printf_("CakeML has sent %c\n", tx);
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
  // warning: cast from pointer to integer of different size
  // end = (char)(&__trusted_heap_end__);
  cml_main(); // Passing control to CakeML
}
#endif
