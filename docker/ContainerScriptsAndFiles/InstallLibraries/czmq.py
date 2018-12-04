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


LIBRARY_NAME="czmq"
LIBRARY_FOLDER_NAME="czmq"
SOURCE_ARCHIVE_FILE="v4.0.2.zip"
SOURCE_ARCHIVE_ADDRESS="https://github.com/zeromq/czmq/archive/"
SOURCE_FOLDER_NAME="czmq-4.0.2"

print( "Making Dirs")
sys.stdout.flush()
CWD=os.getcwd()

callWithShell("mkdir -p ./{}".format(LIBRARY_FOLDER_NAME))
os.chdir(LIBRARY_FOLDER_NAME)

if (os.path.isfile(SOURCE_ARCHIVE_FILE)):
    print("*** {}:: Archive File ({}) Exists, Skipping Source Fetch! ***".format(LIBRARY_NAME,SOURCE_ARCHIVE_FILE))
    sys.stdout.flush()
else:
    print("Fetching Source")
    sys.stdout.flush()
    callWithShell("wget {}{}".format(SOURCE_ARCHIVE_ADDRESS, SOURCE_ARCHIVE_FILE))

print("Unpacking...")
sys.stdout.flush()
callWithShell("unzip -o {}".format(SOURCE_ARCHIVE_FILE))

# change to the source directory
os.chdir(SOURCE_FOLDER_NAME)

print( "Building...")
callWithShell("./autogen.sh")
callWithShell("./configure && make check")

print("Installing...")
sys.stdout.flush()
callWithShell("{} make install".format(_SUDO))
callWithShell("{} ldconfig".format(_SUDO))

print("Cleaning up...")
sys.stdout.flush()
os.chdir(CWD)

# uncomment the following line to remove source code
#callWithShell("rm -rf ./{}".format(LIBRARY_FOLDER_NAME))

print("Finished!")
sys.stdout.flush()
