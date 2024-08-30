# dockerfile with latest compilers
FROM ubuntu:24.04

# TODO move apt-utils install first
# TODO regroup packages

RUN apt-get update && echo
RUN apt-get install -y python3-serial
RUN apt-get install -y flex
RUN apt-get install -y bison
RUN apt-get install -y wget
RUN apt-get install -y git
RUN apt-get install -y make
RUN apt-get install -y tmux
RUN apt-get install -y dash

# RUN apt-get install -y gcc-arm-linux-gnueabihf

RUN apt-get install -y --fix-missing gcc-13-arm-linux-gnueabihf-base
RUN apt-get install -y cpp-13-arm-linux-gnueabihf
RUN apt-get install -y cpp-arm-linux-gnueabihf
RUN apt-get install -y binutils-arm-linux-gnueabihf
RUN apt-get install -y gcc-13-cross-base
RUN apt-get install -y gcc-14-cross-base
RUN apt-get install -y libc6-armhf-cross
RUN apt-get install -y libgcc-s1-armhf-cross
RUN apt-get install -y libgomp1-armhf-cross
RUN apt-get install -y libatomic1-armhf-cross
RUN apt-get install -y libasan8-armhf-cross
RUN apt-get install -y libstdc++6-armhf-cross
RUN apt-get install -y libubsan1-armhf-cross
RUN apt-get install -y libgcc-13-dev-armhf-cross
RUN apt-get install -y gcc-13-arm-linux-gnueabihf
RUN apt-get install -y gcc-arm-linux-gnueabihf
RUN apt-get install -y linux-libc-dev-armhf-cross
RUN apt-get install -y libc6-dev-armhf-cross

RUN apt-get install -y binutils-arm-none-eabi
RUN apt-get install -y gcc-arm-none-eabi
RUN apt-get install -y libnewlib-arm-none-eabi

RUN apt-get install -y g++

RUN apt-get install -y autoconf

RUN apt-get install -y apt-utils

COPY install_polyml.sh /var/
RUN cd /var/ && sh install_polyml.sh

RUN cat <<EOF > /etc/ld.so.conf.d/polyml.conf
# polyml load directory
/usr/local/lib/
EOF

# refresh cache of ld
RUN ldconfig

RUN apt-get install -y curl

COPY install_hol4.sh /var/
RUN cd /var/ && sh install_hol4.sh

COPY install_cakeml.sh /var/
RUN cd /var/ && sh install_cakeml.sh

ENV DOCKER_RUNNING=true
RUN apt-get install -y cpio

RUN apt-get install -y file
RUN apt-get install -y bzip2 bc rsync unzip

RUN apt-get install -y rustup

RUN rustup set auto-self-update disable
# prevents "error: rustup is not installed at '/root/.cargo'"
RUN mkdir /root/.cargo
# set rustc version for required glibc compatibility
RUN rustup install 1.77
RUN rustup default 1.77
RUN rustup target add armv7-unknown-linux-gnueabihf

RUN apt install -y dh-autoreconf

