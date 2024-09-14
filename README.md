# Trustfull Electronic Voting Demonstrator

## Compilation

### clone the repositories and build docker images

```sh
git clone https://github.com/kth-step/evoting-demonstrator.git
cd evoting-demonstrator
```

Expected project directory hierarchy:

```
├── .envrc
├── docker-tevdcompile/
├── docker-xenial-arm-gnueabi-gcc4.7/
├── documentation/
├── evoting-demonstrator/
├── hypervisor/
├── hypervisor-cakeml/
├── lib -> hypervisor-cakeml/lib
├── linux-5.15.13/
└── sources/
```


```sh
# download and import pre-compiled docker images
# Precompiled images are available on request.
docker load --input tevdcompile.tar.gz
docker load --input xenialarm-gcc-4.7.tar.gz

# alternatively build docker images (several hours)
docker build -t tevdcompile docker-tevdcompile/
# alternatively build docker images (several minutes)
docker build -t xenialarmgnueabigcc4.7 docker-xenial-arm-gnueabi-gcc4.7/
```

### enter the docker compile container

At the root of the `hypervisor-total` checkout enter docker:
```sh
docker run --rm --network host -v "$(pwd)":/usr/src/myapp -w /usr/src/myapp -it tevdcompile /bin/bash
```

### in tevdcompile docker

```sh
. .envrc
# check environment variables
env | grep '/usr/src/\|/var/'

# download and build dependencies
make -C $HYP_ROOT/lib cake64 cake32
make -C $HYP_ROOT buildroot-2021.02.8

# expected to fail with `ERROR: vfat(boot.vfat): could not setup MLO`
make -C $HYP_ROOT buildroot-2021.02.8/output/host/bin/arm-linux-gcc

# variant 1) test program
make -C $HYP_ROOT TEST_rs=1 TEST_cml=1

# variant 2) tevd program
make -C $VCSDIR wolfssloutarm/lib/libwolfssl.a
# for full rust traces supply RUST_LINUX_DEBUG=1 to make:
make -C $VCSDIR/crosscompile
make -C $HYP_ROOT

# recompilation of the latter two variants may require `make clean` in the project root
make -C $HYP_ROOT clean
```

As files and directories created by docker are owned by `root` a recompilation
outside of docker with the host machine's compilers will fail. Setting access
rights prior a recompilation via
```sh
sudo chown $USER -R $HYP_ROOT
```
will solve these issues.

### compile hypervisor

Compile hypervisor located at
`$HYP_ROOT/hypervisor/core/build/sth_beaglebone.fw.img`
together with the programs in another docker with a fixed gcc version

```sh
docker run --rm -v "$(pwd)/hypervisor":/usr/src/myapp -w /usr/src/myapp -it xenialarmgnueabigcc4.7 make
```

Once instantiated run:
```sh
. .envrc
# compile test programs:
make TEST_cml=1 TEST_rs=1
# compile mix of test and real programs:
make TEST_cml=1
# compile real programs:
make
```

## Build preparations

- Enable docker image with gcc 4.7 for hypervisor comilation
  ```sh
  docker build -t xenialarmgnueabigcc4.7 docker-xenial-arm-gnueabi-gcc4.7/
  ```
- Run `make deps` to download
  - CakeML compiler for 32-bit and 64-bit
  - [buildroot 2021.02.8](https://buildroot.org/)
    `make buildroot-2021.02.8/output/host/bin/arm-linux-gcc`
    which is allowed to fail at executing post-image script `support/scripts/genimage.sh`

### build dependencies

The below dependencies are pre-compiled in a docker image:
```sh
docker build -t tevdcompile docker-tevdcompile/
```

- HOL4
- GCC compilers
  - GCC compiler (tested with 9.4.0)
  - [arm-none-eabi-gcc](https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads/11-2-2022-02)
    version 11.2-2022.02
  - Ubuntu dependencies
    ```sh
    sudo apt install gcc-arm-linux-gnueabihf binutils-arm-none-eabi \
      gcc-arm-none-eabi libnewlib-arm-none-eabi python3-serial \
      flex bison
    ```
- Docker (may need `systemctl start docker`)
- [`rustup`](https://sh.rustup.rs) with targets:
  `rustup target add armv7-unknown-linux-gnueabihf`
- `python3-serial` for serial connection via `serial.tools.miniterm` instead of
  [c-kermit](http://www.columbia.edu/kermit/ck90.html)
  and add your user to the group `dailout` (on ubuntu via `sudo groupadd $USER dialout`
  otherwise via `sudo usermod -a -G dialout $USER`)
- For the above docker import create group `docker` and add user to it to run
  sudo-less docker. On ubuntu
  ```sh
  sudo groupadd docker
  sudo adduser $USER docker
  newgrp - docker # or login again
  sudo systemctl enable --now  docker # start docker
  ```
  see [docker documentation](https://docs.docker.com/engine/install/linux-postinstall)

### build variables

The build dependencies are set as environment variables denoting paths, and
used across all `Makefile`s. The file `.envrc` sets default values that are
used in docker.

- `HYP_ROOT`: checkout of this [git repository](https://github.com/arolle/hypervisor-total)
- `VCSDIR`: checkout of the [TEVD demonstrator repository](https://github.com/arolle/evoting-demonstrator)
- `HOLDIR`: checkout of [HOL4 repository](https://github.com/HOL-Theorem-Prover/HOL/),
  e.g. commit `fd366fde86123cf8d42ca2530fa10c15fbf14549`
- `CAKEMLDIR`: checkout of [CakeML repository](https://github.com/CakeML/cakeml),
  matching the HOL4 version,
  e.g. commit `9c063a7d92cadb36c49a6e45856ae0db734dc9e5`
- `TOOLCHAIN`: path to Buildroot toolchain, e.g.
  `$HYP_ROOT/output/host/bin/arm-buildroot-linux-uclibcgnueabihf-`
- `CAKEDIR`: path to directory holding `cake64`, `cake32` and `basis_ffi.c` for
  the CakeML 64/32-bit compiler and the basis library, e.g.
  `$HYP_ROOT/hypervisor-cakeml/lib`

---

## Running the demonstrator

The demonstrator is compiled to a bootable image at
```
$HYP_ROOT/hypervisor/core/build/sth_beaglebone.fw.img
```
that can be booted from a Beaglebone Black REV C board (BBB).
The BBB fetches the bootable image over the network from a TFTP server on the
host machine.

### configure the host machine

The host machine needs to host a TFTP server on the proper network, that the
BBB can access.

For networkmanager on linux the settings are as follows:

```
nmcli connection edit StaticNet
set ipv4.addresses 192.100.1.1/24
set ipv4.gateway 192.100.1.1
set ipv4.method manual
remove ipv4.dns
set connection.type ethernet
set never-default
save
verify
activate enp0sxxxx
```

Install and configure the package `tftp-hpa`
and set the file `/etc/conf.d/tftpd` to hold
```
TFTPD_ARGS="--secure $HYP_ROOT/hypervisor --create -v -v -v"
```
with the `$HYP_ROOT` variable expanded.
Start the system service with `systemctl start tftpd`.

An alternative for the host TFTP server setup is the following approach for
Ubuntu (which stems from the hypervisor instructions):

a)	Install following packages:

		sudo apt-get install xinetd tftpd tftp

	b)	Create /etc/xinetd.d/tftp and insert the following lines, where the path
		of server_args identifies the directory containing the files accessible
    through tftp with path to project root being the path expansion of
    `$HYP_ROOT`.

		service tftp
		{
		protocol        = udp
		port            = 69
		socket_type     = dgram
		wait            = yes
		user            = nobody
		server          = /usr/sbin/in.tftpd
		server_args     = <path to project root>/hypervisor
		disable         = no
		flags           = IPv4
		}

	d)	Restart the xinetd service.

    sudo systemctl restart xinetd.service
		sudo /etc/init.d/xinetd stop or sudo service xinetd stop
		sudo /etc/init.d/xinetd start or sudo service xinetd start


### configure the Beaglebone Black

Connect Beaglebone Black
Connect the black cable of the serial-cable (connected to the PC) to the pin with the white dot next to it.
Press the boot `POWER` switch button and insert usb power cable, and release when output is shown in `screen`.
To power off, press the power button until the power led turns off, and remove the power cable while the led is turned off.

#### commands to run on Beaglebone Black within uboot

To boot the proper files, ensure that IP, file
`core/build/sth_beaglebone.fw.img` and start address `0x80000000` are correctly
set on the BBB.
```
setenv bootcmd "tftpboot 0x80000000 192.100.1.1:core/build/sth_beaglebone.fw.img;bootm 0x80000000"
setenv ipaddr 192.100.1.2
setenv bootcount 3
setenv serverip 192.100.1.1
saveenv
printenv
env
bootd # to boot into the linux image over TFTP
```

#### connecting to the Beaglebone Black

Run the serial console via [miniterm from python pyserial package](https://pyserial.readthedocs.io/en/latest/tools.html#miniterm)
in a tmux session enriched to store the log output upon exit with `C-c`.
```sh
make -C $HYP_ROOT runserial
```

Other `miniterm` shortcuts:
```
c-] exit program
C-T C-] send exit character to remote
C-T C-I show info
--- Toggles:
---    Ctrl+R  RTS   Ctrl+D  DTR   Ctrl+B  BREAK
---    Ctrl+E  echo  Ctrl+L  EOL
```

Log in to linux on BBB as `root`.

If networking is not enabled at startup, start networking on BBB Linux:
```sh
/etc/init.d/S60confnet.sh
```

The demonstrator is the executable placed in the root, which is shown when
hitting `ls`.
