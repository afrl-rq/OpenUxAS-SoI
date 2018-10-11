#! /usr/bin/env /usr/bin/python33
import time
import sys
import os
from subprocess import call 

def callWithShell(cmd):
    call(cmd,shell=True)

print("Installing Basic Dependencies for UxAS...")
sys.stdout.flush()

callWithShell("set -e")

_SUDO = 'sudo'
try:
    if (sys.argv[1] == "NO_SUDO"):
        _SUDO = ''
except:
    pass

INSTALL_CWD = os.getcwd()

callWithShell("mkdir -p ./temp")

os.chdir("./temp")

callWithShell("/usr/bin/python3 ../boost.py {}".format(_SUDO))
 # callWithShell("/usr/bin/python3 ../zeromq.sh {}".format(_SUDO))
 # callWithShell("/usr/bin/python3 ../czmq.sh {}".format(_SUDO))
callWithShell("/usr/bin/python3 ../zyre.py {}".format(_SUDO))
callWithShell("/usr/bin/python3 ../cppzmq.py {}".format(_SUDO)) 
callWithShell("/usr/bin/python3 ../sqlite3.py {}".format(_SUDO))
callWithShell("/usr/bin/python3 ../sqlitecpp.py {}".format(_SUDO))
 # callWithShell("/usr/bin/python3 ../zlib.sh {}".format(_SUDO))
 # callWithShell("/usr/bin/python3 ../minizip.sh {}".format(_SUDO))
 # callWithShell("/usr/bin/python3 ../geographiclib.sh {}".format(_SUDO))
 # callWithShell("/usr/bin/python3 ../googletest.sh {}".format(_SUDO))
 # callWithShell("/usr/bin/python3 ../gdal.sh {}".format(_SUDO))

 #../opencv.py {}".format(_SUDO))
 #../ffmpeg.py {}".format(_SUDO))

os.chdir(INSTALL_CWD)
callWithShell("{} rm -rf ./temp".format(_SUDO))

print("Finished installing Basic UxAS dependencies!")
sys.stdout.flush()