#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>
#include <openssl/evp.h>
#include <openssl/decoder.h>

#define printf_(...) { }

// calculates sha256 hash of buffer data and returns digest of length
// SHA256_DIGEST_LENGTH
int sha256(unsigned char * data, size_t datalen, unsigned char * digest) {
  EVP_MD_CTX * ctx = EVP_MD_CTX_new();
  if (!EVP_DigestInit_ex2(ctx, EVP_sha256(), NULL)) {
      printf_("Message digest initialization failed.\n");
      EVP_MD_CTX_free(ctx);
      return -1;
  }

  if (!EVP_DigestUpdate(ctx, data, datalen)){
    printf_("EVP_DigestUpdate failed %d\n", datalen);
    return -1;
  }

  if (!EVP_DigestFinal_ex(ctx, digest, NULL)) {
    printf_("EVP_DigestFinal_ex failed.\n");
    return -1;
  }
  EVP_MD_CTX_free(ctx);
  return 1;
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

  EVP_PKEY *pkey = NULL;

  OSSL_DECODER_CTX *dctx;
  dctx = OSSL_DECODER_CTX_new_for_pkey(&pkey, "PEM", NULL, NULL,
                                      EVP_PKEY_PUBLIC_KEY,
                                      NULL, NULL);

  if (dctx == NULL) {
    printf_("error: no suitable potential decoders found\n");
  }
  const unsigned char * key_data_p = &key[0];
  if (!OSSL_DECODER_from_data(dctx, &key_data_p, &keylen)) {
    printf_("error: decoding failure\n");
  }

  EVP_PKEY_CTX *pctx = NULL;

  pctx = EVP_PKEY_CTX_new(pkey, NULL);
  if (!pctx)
    printf_("error pctx\n");
  if (EVP_PKEY_verify_init(pctx) <= 0)
    printf_("error EVP_PKEY_verify_init\n");
  if (EVP_PKEY_CTX_set_rsa_padding(pctx, RSA_PKCS1_PADDING) <= 0)
    printf_("error EVP_PKEY_CTX_set_rsa_padding\n");
  if (EVP_PKEY_CTX_set_signature_md(pctx, EVP_sha256()) <= 0)
    printf_("error EVP_PKEY_CTX_set_signature_md\n");

  int result = EVP_PKEY_verify(pctx, sign, signlen, digest, SHA256_DIGEST_LENGTH);

  EVP_PKEY_free(pkey);
  EVP_PKEY_CTX_free(pctx);
  OSSL_DECODER_CTX_free(dctx);
  return result;
}

