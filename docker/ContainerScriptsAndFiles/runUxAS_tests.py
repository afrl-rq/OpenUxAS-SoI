#! /usr/bin/env python3
import os
from subprocess import call 

def callWithShell(cmd):
    call(cmd, shell=True)

# 1 - change to the volume with OpenUxAS code :
os.chdir("/tmp_build")

# if `build` exists, then just run Ninja
if(os.path.isdir("build")):
    callWithShell("meson build --buildtype=release")

# 3 - compile the code
callWithShell("ninja -C build test")