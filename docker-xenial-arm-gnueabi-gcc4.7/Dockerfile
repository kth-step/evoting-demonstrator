FROM buildpack-deps:xenial

RUN apt-get update && apt-get install -y \
  make cmake bc

RUN apt-get update && apt-get install -y \
  gcc-4.7-arm-linux-gnueabi \
  && update-alternatives --install /usr/bin/arm-linux-gnueabi-gcc arm-linux-gnueabi-gcc /usr/bin/arm-linux-gnueabi-gcc-4.7 999

RUN apt-get update && apt-get install -y \
  gcc-arm-none-eabi

RUN apt-get update && apt-get install -y \
  u-boot-tools

RUN apt-get update && apt-get install -y \
  cpio rsync

