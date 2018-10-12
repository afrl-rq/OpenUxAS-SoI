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

OPENCV_VERSION=3.1.0
print("Installing OpenCV {}".format(OPENCV_VERSION))
sys.stdout.flush()

callWithShell("mkdir ./temp/OpenCV")

os.chdir("./temp/OpenCV")

print("Installing Dependenices") 
# apt-get -y install libopencv-dev
# apt-get -y install build-essential checkinstall cmake pkg-config yasm
# apt-get -y install libtiff4-dev libjpeg-dev libjasper-dev
# apt-get -y install libavcodec-dev libavformat-dev libswscale-dev libdc1394-22-dev libxine-dev libgstreamer0.10-dev libgstreamer-plugins-base0.10-dev libv4l-dev qt*5-dev
# apt-get -y install python-dev python-numpy

callWithShell("apt-get -y install build-essential")
callWithShell("apt-get -y install cmake git libgtk2.0-dev pkg-config libavcodec-dev libavformat-dev libswscale-dev")
callWithShell("apt-get -y install python-dev python-numpy libtbb2 libtbb-dev libjpeg-dev libpng-dev libtiff-dev libjasper-dev libdc1394-22-dev")

print("Downloading OpenCV {}".format(OPENCV_VERSION))
sys.stdout.flush()

#check if the file exists, if it does skip download
if (os.path.isfile("./opencv-{}.zip".format(OPENCV_VERSION))):
    print("File exists, skipping!")
    sys.stdout.flush()
else:
    callWithShell("wget http://github.com/Itseez/opencv/archive/{}.zip".format(OPENCV_VERSION))
    callWithShell("mv {0}.zip opencv-{0}.zip".format(OPENCV_VERSION))
	
print("Downloading OpenCV Contrib $OPENCV_VERSION")
sys.stdout.flush()

if(os.path.isfile("./opencv-contrib-{}.zip".format(OPENCV_VERSION))):
    print("File exists, skipping!")
    sys.stdout.flush()
else:
    callWithShell("wget http://github.com/Itseez/opencv_contrib/archive/{}.zip".format(OPENCV_VERSION))
    callWithShell("mv $OPENCV_VERSION.zip opencv-contrib-{}.zip".format(OPENCV_VERSION))   

print("Installing OpenCV {}".format(OPENCV_VERSION))
callWithShell("unzip -o opencv-contrib-{}.zip".format(OPENCV_VERSION))
callWithShell("unzip -o opencv-{}.zip".format(OPENCV_VERSION))


if(os.path.isdir("./opencv-{}".format(OPENCV_VERSION))):
    print("Entering OpenCV Dir...")
    sys.stdout.flush()
else:
	print("LAME")
    sys.stdout.flush()
	return

os.chdir("./opencv-{}".format(OPENCV_VERSION))

callWithShell("mkdir build")
os.chdir("build")
callWithShell("cmake -D CMAKE_BUILD_TYPE=DEBUG -D CMAKE_INSTALL_PREFIX=/usr/local -D WITH_CUDA=OFF -D OPENCV_EXTRA_MODULES_PATH=../../opencv_contrib-{}/modules/ .. || exit \"CMAKE FAILED TO CONFIGURE\"".format(OPENCV_VERSION))
callWithShell("make -j4 || exit \"BUILD FAILED\"")
callWithShell("make install")
callWithShell("sh -c 'echo "/usr/local/lib" > /etc/ld.so.conf.d/opencv.conf'")
callWithShell("ldconfig")

print("Cleaning Up...")

os.chdir("../../")
callWithShell("rm -rf opencv-contrib-{}.zip".format(OPENCV_VERSION))
callWithShell("rm -rf opencv-{}.zip".format(OPENCV_VERSION))

os.chdir("../")
callWithShell("rm -rf opencv-{}".format(OPENCV_VERSION))
callWithShell("rm -rf opencv_contrib-{}".format(OPENCV_VERSION))

print("OpenCV {} ready to be used".format(OPENCV_VERSION))
sys.stdout.flush()
