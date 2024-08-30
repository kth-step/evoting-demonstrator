
# Cross compile

- fetch dependencies
  - WolfSSL
    `make -C $VCSDIR wolfssloutarm/lib/libwolfssl.a`
- `.envrc` template
  ```sh
  export HOLDIR=
  export CAKEMLDIR=
  export HYP_ROOT=
  export BUILDROOT="$HYP_ROOT/buildroot-2021.02.8/"
  # path containing cake excutable
  export CAKEDIR=
  ```
- run `. .envrc && make` to produce both `tevdProg.bin` and `out/server`
  ```sh
  make
  cp tevdProg.bin $HYP_ROOT/hypervisor/guests/trusted/build/trusted.bin
  cp tevdProg.bin $HYP_ROOT/hypervisor/guests/trusted/build/trusted.bin
  cp out/server   $HYP_ROOT/rootfs/root/rust_app
  cp out/server   $BUILDROOT/output/images/rootfs/root/rust_app 
  ```
- proceed according to ../../../hypervisor-cakeml/README.md:
  find ./rootfs | cpio -ov > rootfs.cpio
  grep CONFIG_INITRAMFS_SOURCE hypervisor.linux/.config
  make ARCH=arm CROSS_COMPILE=arm-linux-gnueabihf- -j8 -C hypervisor.linux
  cat hypervisor.linux/arch/arm/boot/zImage linux-5.15.13/arch/arm/boot/dts/am335x-boneblack.dtb > hypervisor/guests/linux/build/zImage.bin

# list picked-up library paths
arm-none-eabi-gcc -print-search-dirs

---

# package dependencies for cross compilation

arm-none-eabi-newlib arm-none-eabi-gcc arm-none-eabi-binutils

---

# notes

rustup target list

https://releases.rs/docs/1.70.0/
Rust version 1.70.0 from 1 June, 2023

rustup toolchain install --target ... --profile default 1.70.0
rustup toolchain list | grep '1.70.0'

install target for some toolchain:
ignore: rustup +nightly-2023-01-15-armv7-unknown-linux-gnueabihf target add armv7a-none-eabi
rustup +nightly-2023-01-15-x86_64-unknown-linux-gnu target add armv7a-none-eabi
rustup +nightly-2023-01-15-x86_64-unknown-linux-gnu target add armv7-unknown-linux-gnueabihf

Compile via:
cargo ... +nightly-2023-01-15-... --target=armv7...

armv7r-unknown-none-eabi	Little-endian Cortex-R4/R5 processor (ARMv7-R)
https://github.com/rust-lang/rust/blob/1.52.1/compiler/rustc_target/src/spec/armv7r_none_eabi.rs

armv7a-none-eabi	ARMv7-A target for bare-metal code
https://github.com/rust-lang/rust/blob/1.52.1/compiler/rustc_target/src/spec/armv7a_none_eabi.rs


