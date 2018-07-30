mkdir -p ~/.local/bin
export PATH=~/.local/bin:$PATH

# Homebrew deps for Mac
brew bundle --file=./.Brewfile
export BOOST_ROOT=/usr/local

# install verion of Meson that is compatible with UxAS build
curl -L -s https://github.com/mesonbuild/meson/archive/0.45.0.zip -o meson.zip
unzip -q meson.zip
export PATH=~/Library/Python/3.6/bin:$PATH
pushd meson-0.45.0; python3 setup.py install; popd;
meson --version

# clone, build, and run LmcpGen
git clone https://github.com/afrl-rq/LmcpGen.git ../LmcpGen
pushd ../LmcpGen; ant jar; popd
sh RunLmcpGen.sh

# process the wraps and their patches
./prepare

# build with -j2; Travis has 2 "cores"
meson build
ninja -C build -j2
# run test suite with *2 timeout multiplier, because Travis can be slow
meson test --print-errorlogs -C build -t 2
