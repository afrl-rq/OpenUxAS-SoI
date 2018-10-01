#!/bin/bash -e

# 1 - change to the volume with OpenUxAS code :
cd /tmp_build

# if `build` exists, then just run Ninja
if [ ! -d "build" ]; then
	meson build --buildtype=release
fi

# 3 - compile the code
ninja -C build test