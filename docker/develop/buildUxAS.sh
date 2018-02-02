#!/bin/bash -e

IS_INTERNAL=$1
USE_INTERNAL="false"
if [ "$IS_INTERNAL" = "true" ]
then
    USE_INTERNAL="true"
fi

# 1 - change to the directory: OpenUxAS
cd /UxASDev/OpenUxAS

# 2
# if "build" exists the just run Ninja
if [ ! -d "build" ]; then
    echo "##### NEW MESON BUILD DIRECTORY #####"
    meson build  -Dafrl_internal=${USE_INTERNAL} --buildtype=release
else
    echo "##### USING EXISTING MESON BUILD DIRECTORY #####"
    cd build
    meson configure -Dafrl_internal=${USE_INTERNAL}
    cd ..
fi

# 3 - compile the code
ninja -C build all
