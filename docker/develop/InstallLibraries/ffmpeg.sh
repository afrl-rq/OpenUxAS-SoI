arch=$(uname -m)
if [ "$arch" == "i686" -o "$arch" == "i386" -o "$arch" == "i486" -o "$arch" == "i586" ]; then
flag=1
else
flag=0
fi
echo "Installing the dependencies for FFMPEG"
 apt-get update
 apt-get -y install autoconf automake build-essential libass-dev libfreetype6-dev libsdl1.2-dev libtheora-dev libtool libva-dev libvdpau-dev libvorbis-dev libxcb1-dev libxcb-shm0-dev libxcb-xfixes0-dev pkg-config texinfo zlib1g-dev
echo "Create folder to house the sources"
mkdir ~/ffmpeg_sources
mkdir ~/ffmpeg_build
mkdir ~/bin
echo "Download and compile dependencies"
#Yasm
 apt-get -y install yasm
#libx264
 apt-get -y install libx264-dev
#libmp3lame
 apt-get -y install libmp3lame-dev
#libopus
 apt-get -y install libopus-dev
echo "Installing FFMPEG"
cd ~/ffmpeg_sources
wget http://ffmpeg.org/releases/ffmpeg-snapshot.tar.bz2
tar xjvf ffmpeg-snapshot.tar.bz2
cd ffmpeg
#PATH="/usr/bin:$PATH" PKG_CONFIG_PATH="/usr/lib/pkgconfig" ./configure \
#  --prefix="/usr/lib" \
#  --enable-shared \
#  --extra-cflags="-I/usr/include/arm-linux-gnueabihf" \
#  --extra-ldflags="-L/usr/lib/arm-linux-gnueabihf" \
#  --bindir="/usr/bin" \
PATH="$HOME/bin:$PATH" PKG_CONFIG_PATH="$HOME/ffmpeg_build/lib/pkgconfig" ./configure \
  --prefix="$HOME/ffmpeg_build" \
#  --pkg-config-flags="--static" \
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
  --enable-nonfree
PATH="/usr/bin:$PATH" make
make install
make distclean
hash -r

