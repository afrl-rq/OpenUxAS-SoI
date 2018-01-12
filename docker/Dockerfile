FROM ubuntu:16.04

RUN apt-get update && apt-get install -y \
  bc \
  build-essential \
  cpio \
  git \
  python \
  unzip \
  wget

WORKDIR /src

RUN git  clone -b odroidxu4_uxas https://github.com/acfoltzer/buildroot.git

RUN make -C buildroot odroidxu4_uxas_defconfig
RUN make -C buildroot sdk
