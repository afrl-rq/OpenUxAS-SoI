#! /usr/bin/env python3
import time
import sys
import os
import subprocess
from subprocess import call 

def callWithShell(cmd):
    process = subprocess.Popen(cmd,shell=True)
    process.wait()

startAllTime = time.time()

print("\n*** Sync Files ### \n")
sys.stdout.flush()

callWithShell("python /UxASDev/OpenUxAS/docker/ContainerScriptsAndFiles/syncUxASFiles.py")

print("\n#### RUNNING MESON ####\n")
sys.stdout.flush()

mesonStartTime = time.time()

# 1 - change to the directory: OpenUxAS
os.chdir("/tmp_build")

# 2
# if "build" exists the just run Ninja
if(not os.path.isdir("build")):
    print("##### NEW MESON BUILD DIRECTORY #####")
    callWithShell("meson build  --buildtype=release")

print("\n#### FINISHED RUNNING MESON [{}] ####\n".format(time.time() - mesonStartTime))
sys.stdout.flush()
print("\n#### RUNNING NINJA ####\n")
sys.stdout.flush()

ninjaStartTime = time.time()

# 3 - compile the code
callWithShell("ninja -C build all")

# use meson start time
print("\n#### FINISHED-RUNNING NINJA [{}] ####\n".format(time.time() - ninjaStartTime))
sys.stdout.flush()

callWithShell("mkdir -p /UxASDev/OpenUxAS/docker/tmp")
callWithShell("cp /tmp_build/build/uxas /UxASDev/OpenUxAS/docker/tmp/uxas")

print("\n#### FINISHED! Total Time [{}] ####\n".format(time.time() - startAllTime))
sys.stdout.flush()