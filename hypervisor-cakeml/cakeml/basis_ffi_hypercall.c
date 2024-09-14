#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>

extern void int_to_byte2(int i, unsigned char *b);
extern int byte2_to_int(unsigned char *b);

// Upon input in a calculates the output in-place in
//   a[0..<*alen] buffer
void ffihypercall (unsigned char *c, long clen, unsigned char *a, long alen) {
  // mock functionality -- later handled by Rust
  assert(alen >= 0);
  unsigned char type = a[0];
  size_t len = (size_t) byte2_to_int(&a[1]);

  printf("  c: hypercall (msg type %d, a) = ...\n", type);
  if (type == 0) {
    a[0] = 0; // set answer type
  } else if (type == 2) {
    a[0] = 0; // set answer type
  } else if (type == 1) {
    a[0] = 1; // set answer type
    char buf[] = "argument1";
    size_t min_len = strlen(buf) < alen - 3 ? strlen(buf) : alen - 3;
    memcpy(&a[3], buf, min_len);
    int_to_byte2((int) min_len, &a[1]);
    printf("  c: copy %d bytes\n", min_len);
  }
  // artificial delay of 1 sec
  sleep(1);
}

