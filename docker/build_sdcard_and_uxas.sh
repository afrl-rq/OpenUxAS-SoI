#!/usr/bin/env bash

set -e

if [ ! -f docker/Dockerfile ]; then
    echo '[build_sdcard_and_uxas.sh] `docker/Dockerfile` not found; are you running this script from the root of OpenUxAS?'
    exit 1
fi

echo '[build_sdcard_and_uxas.sh] Building Docker image; this will take a while'

docker build -t afrl-rq/openuxas docker/

echo '[build_sdcard_and_uxas.sh] Docker image built; extracting SD card image to `/OpenUxAS/sdcard.img`'

docker run --rm -v $(pwd):/src/OpenUxAS afrl-rq/openuxas sh -c 'cp -r /opt/uxas/sdcard.img /src/OpenUxAS/sdcard.img'

echo '[build_sdcard_and_uxas.sh] Cross-compiling UxAS to `/OpenUxAS/build_cross/uxas`'

docker run --rm -v $(pwd):/src/OpenUxAS afrl-rq/openuxas sh -c "rm -rf build_cross && \
python3 rm-external && \
python3 prepare && \
meson.py build_cross --cross-file docker/odroid-xu4-gnueabihf.txt && \
ninja -C build_cross uxas \
"
