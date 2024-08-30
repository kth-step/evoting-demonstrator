#include <stdio.h>

void ffiprintf(unsigned char *c, long clen, unsigned char *string, long string_len) {
  for (int i = 0; i < string_len; i++)
      printf("%c", string[i]);
}

