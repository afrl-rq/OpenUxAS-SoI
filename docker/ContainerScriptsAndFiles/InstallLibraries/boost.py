#! /usr/bin/env python3
import time
import sys
import os
import subprocess
from subprocess import call 

def callWithShell(cmd):
    process = subprocess.Popen(cmd, shell=True)#, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.PIPE, bufsize=1)
    process.wait()
    #call(cmd,shell=True)

#if an argument is being passed @ 1, then try to set as _SUDO
_SUDO= ''
try:
    _SUDO=sys.argv[1]
except:
    pass

# exit on non-zero return
callWithShell("set -e")


#BUILD_TYPE="AUTOCONFIG"
#BUILD_TYPE="AUTOTOOLS"
BUILD_TYPE="BOOST"
#BUILD_TYPE="CMAKE"
#BUILD_TYPE="MAKE"

LIBRARY_NAME="boost"
LIBRARY_FOLDER_NAME="boost"
SOURCE_ARCHIVE_FILE="boost_1_67_0.tar.bz2"
SOURCE_ARCHIVE_ADDRESS="https://dl.bintray.com/boostorg/release/1.67.0/source/"
SOURCE_FOLDER_NAME="boost_1_67_0"

ARCHIVE_COMMAND="tar xjf "

print("Making Dirs")
sys.stdout.flush()
CWD = os.getcwd()
#DELETE PRINT
#making directory boost

callWithShell("mkdir -p ./{}".format(LIBRARY_FOLDER_NAME))
os.chdir(LIBRARY_FOLDER_NAME)

#have to check if file exists in LIBRARY_FOLDER_NAME
if (os.path.isfile(SOURCE_ARCHIVE_FILE)):
    print("*** {}:: Archive File ({}) Exists, Skipping Source Fetch! ***".format(LIBRARY_NAME,SOURCE_ARCHIVE_FILE))
    sys.stdout.flush()
else:
    print("Fetching Source")
    sys.stdout.flush()
    callWithShell("wget {}{}".format(SOURCE_ARCHIVE_ADDRESS, SOURCE_ARCHIVE_FILE))

print("Unpacking...")
sys.stdout.flush()
#unzip -o ${SOURCE_ARCHIVE_FILE}
callWithShell("{} {}".format( ARCHIVE_COMMAND, SOURCE_ARCHIVE_FILE))
#callWithShell("{} {}".format( ARCHIVE_COMMAND, SOURCE_ARCHIVE_FILE))
#race condition

# change to the source directory
os.chdir(SOURCE_FOLDER_NAME)
print("Building...")
sys.stdout.flush()

if(BUILD_TYPE == "AUTOCONFIG"):
    callWithShell("chmod +x configure")
    callWithShell("./configure --prefix=/usr/local")
    callWithShell("make -j8; make")

    print("Installing...")
    sys.stdout.flush()
    callWithShell("{} make install".format(_SUDO))
elif (BUILD_TYPE == "AUTOTOOLS"):
    callWithShell("./autogen.sh")
    callWithShell("./configure && make check")
    print("Installing...")
    sys.stdout.flush()
    callWithShell("{} make install".format(_SUDO))
    callWithShell("{} ldconfig".format(_SUDO))
elif (BUILD_TYPE == "BOOST"):
    callWithShell("export CPLUS_INCLUDE_PATH=\"$CPLUS_INCLUDE_PATH:/usr/include/python2.7/\"")
    #callWithShell("./bootstrap --prefix=/usr/local --with-libraries=all")
    #callWithShell("./bootstrap --prefix=/usr/local cxxflags=\"-stdlib=libc++ -std=c++11 -DLINUX\" linkflags=\"-stdlib=libc++ -std=c++11 -DLINUX\"  --with-libraries=all")
    callWithShell("./bootstrap.sh --prefix=/usr/local cxxflags=\"-stdlib=libc++ -std=c++11 -DLINUX\" linkflags=\"-stdlib=libc++ -std=c++11 -DLINUX\"")
    #callWithShell("./bootstrap --prefix=/usr/local cxxflags=\"-stdlib=libc++ -std=c++11 -DLINUX\" linkflags=\"-stdlib=libc++ -std=c++11 -DLINUX\"  --with-libraries=date_time,filesystem,regex,system,contract")
    callWithShell("{} ./b2 install -d0 threading=multi".format(_SUDO))
    callWithShell("{} ldconfig".format(_SUDO))

elif (BUILD_TYPE == "CMAKE"):
    callWithShell("mkdir -p ./build")
    os.chdir("./build")
    callWithShell("cmake ..")
    callWithShell("make -j8; make")
    print("Installing...")
    sys.stdout.flush()
    callWithShell("{} make install".format(_SUDO))
elif (BUILD_TYPE == "MAKE"):
    callWithShell("make")
    callWithShell("{} make install".format(_SUDO))
else:
    print("!!! UNKNOWN BUILD TYPE [{}]".format(BUILD_TYPE))
    sys.stdout.flush()


print("Cleaning up...")
sys.stdout.flush()
os.chdir(CWD)

# uncomment the following line to remove source code
#callWithShell("{} rm -rf ./{}".format(_SUDO, LIBRARY_FOLDER_NAME))

print("Finished!")
sys.stdout.flush()
