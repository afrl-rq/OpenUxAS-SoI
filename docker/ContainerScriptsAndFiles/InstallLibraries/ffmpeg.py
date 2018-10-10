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

#os.uname is specific to linux?
arch = os.uname()

flag = 0
if (arch == "i686" or arch == "i386" or arch == "i486" or arch == "i586"):
    flag = 1

print("Installing the dependencies for FFMPEG")
sys.stdout.flush()

callWithShell("apt-get update")
callWithShell("apt-get -y install autoconf automake build-essential libass-dev libfreetype6-dev libsdl1.2-dev libtheora-dev libtool libva-dev libvdpau-dev libvorbis-dev libxcb1-dev libxcb-shm0-dev libxcb-xfixes0-dev pkg-config texinfo zlib1g-dev")
print("Create folder to house the sources")
sys.stdout.flush()

callWithShell("mkdir ~/ffmpeg_sources")
callWithShell("mkdir ~/ffmpeg_build")
callWithShell("mkdir ~/bin")

print("Download and compile dependencies")
sys.stdout.flush()
#Yasm

callWithShell("apt-get -y install yasm")
#libx264
callWithShell("apt-get -y install libx264-dev")
#libmp3lame
callWithShell("apt-get -y install libmp3lame-dev")
#libopus
callWithShell("apt-get -y install libopus-dev")
print("Installing FFMPEG")
sys.stdout.flush()
os.chdir("~/ffmpeg_sources")
callWithShell("wget http://ffmpeg.org/releases/ffmpeg-snapshot.tar.bz2")
callWithShell("tar xjvf ffmpeg-snapshot.tar.bz2")
os.chdir("ffmpeg")
#PATH="/usr/bin:$PATH" PKG_CONFIG_PATH="/usr/lib/pkgconfig" ./configure \
#  --prefix="/usr/lib" \
#  --enable-shared \
#  --extra-cflags="-I/usr/include/arm-linux-gnueabihf" \
#  --extra-ldflags="-L/usr/lib/arm-linux-gnueabihf" \
#  --bindir="/usr/bin" \
PATH = "$HOME/bin:$PATH"
PKG_CONFIG_PATH="$HOME/ffmpeg_build/lib/pkgconfig"
callWithShell('./configure --prefix="$HOME/ffmpeg_build" \
                --extra-cflags="-I$HOME/ffmpeg_build/include" \
                --extra-ldflags="-L$HOME/ffmpeg_build/lib" \
                --bindir="$HOME/bin" \
                --enable-gpl \
                --enable-libass \
                --enable-libfreetype \
                --enable-libmp3lame \
                --enable-libopus \
                --enable-libtheora \
                --enable-libvorbis \
                --enable-libx264 \
                --enable-nonfree')
callWithShell('PATH="/usr/bin:$PATH" make')
callWithShell("make install")
callWithShell("make distclean")
callWithShell("hash -r")

