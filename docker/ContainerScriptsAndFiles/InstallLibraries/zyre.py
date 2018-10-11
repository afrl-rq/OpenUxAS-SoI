#! /usr/bin/env python3
import time
import sys
import os
import subprocess
from subprocess import call 

def callWithShell(cmd):
    process = subprocess.Popen(cmd, shell=True)
    process.wait()
    #call(cmd,shell=True)

#if an argument is being passed @ 1, then try to set as _SUDO
_SUDO= ''
try:
    _SUDO=sys.argv[1]
except Exception:
    pass

# exit on non-zero return
callWithShell("set -e")

LIBRARY_NAME="zyre"
LIBRARY_FOLDER_NAME="zyre"
SOURCE_ARCHIVE_FILE="v2.0.0.zip"
SOURCE_ARCHIVE_ADDRESS="https://github.com/zeromq/zyre/archive/"
SOURCE_FOLDER_NAME="zyre-2.0.0"

print("Making Dirs")
CWD=os.getcwd()
callWithShell("mkdir -p ./{}".format(LIBRARY_FOLDER_NAME))

os.chdir("./{}".format(LIBRARY_FOLDER_NAME))

if(os.path.isfile(SOURCE_ARCHIVE_FILE)):
    print("*** \"{}\":: Archive File (\"{}\") Exists, Skipping Source Fetch! ***".format(LIBRARY_NAME, SOURCE_ARCHIVE_FILE))
else:
    print("Fetching Source")
    callWithShell("wget {}{}".format(SOURCE_ARCHIVE_ADDRESS, SOURCE_ARCHIVE_FILE))

print("Unpacking...")
sys.stdout.flush()
callWithShell("unzip -o {}".format(SOURCE_ARCHIVE_FILE))

# change to the source directory
os.chdir(SOURCE_FOLDER_NAME)

print("Building...")
sys.stdout.flush()

callWithShell("./autogen.sh")
callWithShell("./configure --disable-shared && make check")
print("Installing...")
callWithShell("{} make install".format(_SUDO))
callWithShell("{} ldconfig".format(_SUDO))

print("Cleaning up...")
os.chdir(CWD)

# uncomment the following line to remove source code
#callWithShell("rm -rf ./{}".format(LIBRARY_FOLDER_NAME))

print("Finished!")
sys.stdout.flush()
