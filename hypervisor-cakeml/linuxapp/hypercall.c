#include <stddef.h>
#include <stdio.h>

void int_to_byte2(int i, unsigned char *b){
    /* i is encoded on 2 bytes */
    b[0] = (i >> 8) & 0xFF;
    b[1] = i & 0xFF;
}

int byte2_to_int(unsigned char *b){
    return ((b[0] << 8) | b[1]);
}

// Upon input as
//   c[0..*clen] input buffer
// calculates the output as
//   a[0..<*alen] output buffer
void hypercall(unsigned char *c, size_t *clen, unsigned char *a, size_t *alen) {
  // dummy functionality -- later handled by CakeML
  size_t capacity = *alen;
  if (capacity == 0) return;
  if (c[0] == 1) {
    size_t len = (size_t) byte2_to_int(&c[1]);
    printf("  c: input is node's name, len: %d\n  c: ", len);
    for (int i = 0; i < len; i++) {
      printf("%c", c[i+3]);
    }
    printf("\n");
    a[0] = 0; // set response
  } else if (c[0] == 0) {
    printf("  c: input is empty\n");
    a[0] = 1; // ask for "get_self"
  }
  a[3] = a[3]+1; // noise
  // *alen = 3; // new total capacity (less than capacity)
}

