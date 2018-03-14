#!/usr/bin/env bash

DOCKER_NO_CACHE=""

while getopts ":f" opt; do
    case $opt in
        f)
            DOCKER_NO_CACHE="--no-cache"
            echo "[01_build_sdcard_and_sdk.sh] Building Docker image without cache" >&2
            ;;
        \?)
            echo "[01_build_sdcard_and_sdk.sh] Invalid option: -$OPTARG" >&2
            ;;
    esac
done

TOP=$(pwd)

set -e

if [ ! -f $TOP/docker/odroidxu4/Dockerfile ]; then
    echo '[01_build_sdcard_and_sdk.sh] `docker/odroidxu4/Dockerfile` not found; are you running this script from the root of OpenUxAS?'
    exit 1
fi

echo '[01_build_sdcard_and_sdk.sh] Building Docker image; this will take a while the first time'

docker build $DOCKER_NO_CACHE -t uxas_cross $TOP/docker/odroidxu4

echo '[01_build_sdcard_and_sdk.sh] Docker image built; extracting SD card image to `/OpenUxAS/sdcard.img`'

docker run --rm -v $TOP:/src/OpenUxAS uxas_cross sh -c 'cp -r /opt/uxas/sdcard.img /src/OpenUxAS/sdcard.img'

echo '[01_build_sdcard_and_sdk.sh] Preparing 3rd party dependencies'

# clean up any old containers in case a previous run errored out
docker rm uxas_cross_deps &> /dev/null || true
# populate the packagecache
docker run --name uxas_cross_deps -v $TOP:/src/OpenUxAS uxas_cross sh -c "\
rm -rf build_tmp_for_deps_fetching && \
python3 ./rm-external && \
python3 ./prepare && \
meson.py build_tmp_for_deps_fetching \
  --cross-file docker/odroidxu4/odroid-xu4-gnueabihf.txt && \
rm -rf build_tmp_for_deps_fetching && \
mkdir -p /var/cache/OpenUxAS/3rd && \
cp -r 3rd/packagecache /var/cache/OpenUxAS/3rd/ \
"
# save the container state as the new uxas_cross image
docker commit uxas_cross_deps uxas_cross
# clean up the container
docker rm uxas_cross_deps

echo '[01_build_sdcard_and_sdk.sh] Resetting permissions in `/OpenUxAS` and subdirectories'

docker run --rm -v $(pwd):/src/OpenUxAS uxas_cross sh -c "chown -R $(id -u):$(id -g) ."
