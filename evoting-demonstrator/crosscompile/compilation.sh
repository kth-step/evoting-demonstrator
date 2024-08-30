
export VCSDIR=/home/arolle/Projects/Verificatum/verified

export VCSDIR=/home/arolle/Documents/verified/

. .envrc

cd $VCSDIR/wolfssl/
make clean
git clean -xdf
./autogen.sh
rm -rf ../wolfssl-arm-new
mkdir ../wolfssl-arm-new
./configure \
  --host=arm-non-eabi \
  CC=arm-none-eabi-gcc \
  AR=arm-none-eabi-ar \
  STRIP=arm-none-eabi-strip \
  RANLIB=arm-none-eabi-ranlib \
  --prefix=$(pwd)/../wolfssl-arm-new \
  CFLAGS="-march=armv8-a --specs=nosys.specs \
      -DHAVE_PK_CALLBACKS -DWOLFSSL_USER_IO -DNO_WRITEV \
      -DTIME_T_NOT_64BIT \
      -DNO_WOLFSSL_SERVER -DNO_PWDBASED \
      -DNO_SIMPLE_SERVER -DNO_SIMPLE_CLIENT \
      -DNO_MD5 -DNO_MD4 -DNO_SESSION_CACHE -DNO_RC4 \
      -DNO_DEV_URANDOM -DNO_RESUME_SUITE_CHECK -DNO_OLD_TLS \
      -DNO_SHA -DNO_DSA -DNO_DES3 \
      -DWOLFSSL_NO_SOCK \
    " \
    --disable-benchmark \
    --disable-brainpool \
    --disable-chacha \
    --disable-crypttests \
    --disable-des3 \
    --disable-dh \
    --disable-errorstrings \
    --disable-examples  \
    --disable-filesystem \
    --disable-inline \
    --disable-md5 \
    --disable-md5 \
    --disable-oldtls \
    --disable-pkcs12 \
    --disable-poly1305 \
    --disable-sha3 \
    --disable-shared \
    --disable-sp \
    --disable-sys-ca-certs \
    --disable-tlsv12 \
    --enable-fastmath \
    --enable-opensslall \
    --enable-reproducible-build \
    --enable-singlethreaded
make
make install
cd $VCSDIR/c_crypto_lib
touch wolfsslcrypto.c
make ARCH=arm WOLFSSL=1
cd $VCSDIR/crosscompile/
make

