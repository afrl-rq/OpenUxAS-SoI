#!/usr/bin/env bash

DOCKER_NO_CACHE=""

while getopts ":f" opt; do
    case $opt in
        f)
            DOCKER_NO_CACHE="--no-cache"
            echo "[build_sdcard_and_uxas.sh] Building Docker image without cache" >&2
            ;;
        \?)
            echo "[build_sdcard_and_uxas.sh] Invalid option: -$OPTARG" >&2
            ;;
    esac
done

set -e

if [ ! -f docker/odroidxu4/Dockerfile ]; then
    echo '[build_sdcard_and_uxas.sh] `docker/odroidxu4/Dockerfile` not found; are you running this script from the root of OpenUxAS?'
    exit 1
fi

echo '[build_sdcard_and_uxas.sh] Building Docker image; this will take a while the first time'

docker build $DOCKER_NO_CACHE -t uxas_cross docker/odroidxu4

echo '[build_sdcard_and_uxas.sh] Docker image built; extracting SD card image to `/OpenUxAS/sdcard.img`'

docker run --rm -v $(pwd):/src/OpenUxAS uxas_cross sh -c 'cp -r /opt/uxas/sdcard.img /src/OpenUxAS/sdcard.img'

echo '[build_sdcard_and_uxas.sh] Cross-compiling UxAS to `/OpenUxAS/build_cross/uxas`'

docker run --rm -v $(pwd):/src/OpenUxAS uxas_cross sh -c "rm -rf build_cross && \
python3 rm-external && \
python3 prepare && \
meson.py build_cross --cross-file docker/odroidxu4/odroid-xu4-gnueabihf.txt && \
ninja -C build_cross uxas \
"
