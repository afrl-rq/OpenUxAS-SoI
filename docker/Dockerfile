FROM ubuntu:artful

RUN apt-get update && apt-get install -y \
  bc \
  build-essential \
  cpio \
  device-tree-compiler \
  git \
  python \
  rsync \
  unzip \
  wget

WORKDIR /src

RUN git  clone -b odroidxu4_uxas https://github.com/acfoltzer/buildroot.git

RUN make -C buildroot odroidxu4_uxas_defconfig
RUN make -C buildroot sdk

FROM ubuntu:artful

COPY --from=0 /src/buildroot/output/images/sdcard.img /opt/uxas/sdcard.img
COPY --from=0 /src/buildroot/output/host /opt/arm-buildroot-linux-gnueabihf
RUN cd /opt/arm-buildroot-linux-gnueabihf && sh relocate-sdk.sh

RUN apt-get update && apt-get install -y \
  build-essential \
  curl \
  git \
  ninja-build \
  python3 \
  python3-pip \
  qemu-user-static

RUN curl https://sh.rustup.rs -sSf -o /opt/rustup.sh
RUN sh /opt/rustup.sh -y
ENV PATH="/root/.cargo/bin:${PATH}"
RUN rustup target install armv7-unknown-linux-gnueabihf

WORKDIR /src
RUN git clone -b rust-cross-merge https://github.com/acfoltzer/meson.git
RUN mkdir -p /usr/local/lib/python3.6/site-packages && cd meson && pip3 install -e .

WORKDIR /src/OpenUxAS
VOLUME /src/OpenUxAS

ENV PKG_CONFIG_PATH /opt/arm-buildroot-linux-gnueabihf/arm-buildroot-linux-gnueabihf/sysroot/usr/lib/pkgconfig
