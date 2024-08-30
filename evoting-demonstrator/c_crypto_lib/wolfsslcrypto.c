#include <wolfssl/options.h>
#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/rsa.h>
#include <wolfssl/wolfcrypt/sha256.h>
#include <wolfssl/openssl/pem.h>
#include <wolfssl/openssl/bio.h>
#include <wolfssl/openssl/evp.h>

#ifdef DEBUG
#include <stdio.h>
#define printf_ printf
#else
#define printf_(...) { }
#endif

// calculates sha256 hash of buffer data and returns digest of length
// SHA256_DIGEST_LENGTH
int sha256(unsigned char * data, size_t datalen, unsigned char * digest) {
 return wc_Sha256Hash(data, datalen, digest);
}

// ret == 1 indicates success
int verify(
    unsigned char * data, size_t datalen,
    unsigned char * sign, size_t signlen,
    unsigned char * key,  size_t keylen) {

  // Buffer to hold the calculated digest
  unsigned char digest[SHA256_DIGEST_LENGTH];
  if (sha256(data, datalen, digest) < 0) {
    printf_("failed to compute hash\n");
    return 1;
  }

  printf_("SHA256[%d] = ", SHA256_DIGEST_LENGTH);
  for (int i = 0; i < SHA256_DIGEST_LENGTH; i++)
      printf_("%02x", digest[i]);
  printf_("\n");

  BIO* bio = BIO_new(BIO_s_mem());
  int len = BIO_write(bio, key, keylen);
  EVP_PKEY* evp_key = PEM_read_bio_PUBKEY(bio, NULL, NULL, NULL);
  RSA * rsa_pubkey = EVP_PKEY_get1_RSA(evp_key);
  EVP_PKEY_free(evp_key);
  BIO_free(bio);

  int result = RSA_verify(NID_sha256, digest, SHA256_DIGEST_LENGTH,
                          sign, signlen, rsa_pubkey);
  RSA_free(rsa_pubkey);

  return result;
}

