#!/usr/bin/env bash

set -e

TOP=$(pwd)

if [ ! -f $TOP/docker/odroidxu4/Dockerfile ]; then
    echo '[02_cross_compile_uxas.sh] `docker/odroidxu4/Dockerfile` not found; are you running this script from the root of OpenUxAS?'
    exit 1
fi

echo '[02_cross_compile_uxas.sh] Cross-compiling UxAS to `/OpenUxAS/build_cross/uxas`'

docker run --rm -v $(pwd):/src/OpenUxAS uxas_cross sh -c "rm -rf build_cross && \
cp -r /var/cache/OpenUxAS/3rd . && \
meson.py build_cross \
  --buildtype release \
  --cross-file docker/odroidxu4/odroid-xu4-gnueabihf.txt && \
ninja -C build_cross uxas \
"

echo '[02_cross_compile_uxas.sh] Resetting permissions in `/OpenUxAS` and subdirectories'

docker run --rm -v $(pwd):/src/OpenUxAS uxas_cross sh -c "chown -R $(id -u):$(id -g) ."
