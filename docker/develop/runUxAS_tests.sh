#!/bin/bash -e

# 1 - change to the directory: OpenUxAS
cd /UxASDev/OpenUxAS

# if builds exists the just run Ninja
if [ ! -d "build" ]; then
	meson build --buildtype=release
fi

# 3 - compile the code
ninja -C build test