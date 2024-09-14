#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

extern void int_to_byte2(int i, unsigned char *b);

void ffiecho (unsigned char *c, long clen, unsigned char *a, long alen) {
  unsigned char s[clen+1];
  memcpy(s, c, clen);
  s[clen+1]='\0';
  printf("c: input c = %s\n", s);

  // write back into a
  assert(alen >= clen * 2 + 2);

  // char ret_buf[] = RPC_call(c, clen)
  // memcpy(a, ret_buf, alen)

  // set header: length of data
  int_to_byte2(clen * 2, a);
  // set data: a = c c (two copies of input)
  memcpy(&a[2], c, clen);
  memcpy(&a[clen+2], c, clen);
  printf("c: buffer a = ");
  for (int i = 0; i < alen; i++)
    printf("%02X ", a[i]);
}

