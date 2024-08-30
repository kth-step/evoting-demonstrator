#include <stddef.h>

#ifdef DEBUG
#include <assert.h>
#include <stdio.h>
#define printf_ printf
#else
#define printf_(...) { }
#define assert(...) { }
#endif

#include "keys.h"

extern int sha256(unsigned char * data, size_t datalen, unsigned char * digest);
extern int verify( unsigned char * data, size_t datalen, unsigned char * sign, size_t signlen, unsigned char * key,  size_t keylen);

void my_int_to_byte2(int i, unsigned char *b){
    /* i is encoded on 2 bytes */
    b[0] = (i >> 8) & 0xFF;
    b[1] = i & 0xFF;
}

int my_byte2_to_int(unsigned char *b){
    return ((b[0] << 8) | b[1]);
}

/*
void hexdump(const void *buffer, size_t buf_len, char columns) {
   size_t i;
   size_t limit = buf_len + ((buf_len % columns) ? (columns - buf_len % columns) : 0)
   for(i = 0; i < limit; i++) {
      if (i < buf_len)
         printf_("0x%02X, ", ((char*)buffer)[i] & 0xFF);
      if (i % columns == (columns - 1))
         printf_("\n");
   }
}
*/

void fficrypto_verify_rs256 (unsigned char *c, long clen, unsigned char *a, long alen) {
  printf_("\n");
  int header = 4;
  assert(header <= alen);

  size_t sign_len = my_byte2_to_int(a);
  size_t payload_len = my_byte2_to_int(&a[2]);
  printf_("header 4, sign_len %d, payload_len %d\n", sign_len, payload_len);
  assert(header + sign_len + payload_len <= alen);

  unsigned char * key_data = &freja_pk_2023[0];
  size_t key_data_len = sizeof(freja_pk_2023);

  char sign[sign_len];
  for (int i = 0; i < sign_len; i++) {
    sign[i] = a[header + i];
  }

  char payload[payload_len];
  for (int i = 0; i < payload_len; i++) {
    payload[i] = a[header + sign_len + i];
  }

/*
// debug
printf_("payload\n");
hexdump(payload, payload_len, 0x0F);
printf_("sign\n");
hexdump(sign, sign_len, 0x0F);
printf_("key_data\n");
hexdump(key_data, key_data_len, 0x0F);
/* */

  // returns 0 on failure, 1 on success
  a[0]=!verify(payload, payload_len, sign, sign_len, key_data, key_data_len);
  printf_("[fficrypto_verify_rs256] end. result = %d\n", a[0]);
}

void fficrypto_sha256 (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(32 <= alen);
  size_t buflen = my_byte2_to_int(a);
  char hash[32];
  int n = sha256(&a[2], buflen, hash);
  for (int i = 0; i < 32; i++) {
    a[i]=hash[i];
  }
}

