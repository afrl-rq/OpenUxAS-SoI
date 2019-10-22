#!/bin/bash
# Copyright © 2017 Government of the United States of America, as represented by the Secretary of the Air Force.
# No copyright is claimed in the United States under Title 17, U. S. Code. All Other Rights Reserved.
# Copyright 2017 University of Cincinnati. All rights reserved. See LICENSE.md file at:
# https://github.com/afrl-rq/OpenUxAS
# Additional copyright may be held by others, as reflected in the commit history.

# from the README.md, 2017-05-11:


# references:
# * http://stackoverflow.com/questions/3466166/how-to-check-if-running-in-cygwin-mac-or-linux/17072017#17072017
# * https://serverfault.com/questions/501230/can-not-seem-to-get-expr-substr-to-work

if [ "$(uname)" == "Darwin" ]; then
    echo "Install Prerequisites on Mac OS X"
    echo " "
    echo "Install XCode"
    echo "* Get yourself a developer account and grab the file from: https://developer.apple.com/xcode/"
    echo " (This cannot be downloaded automatically due to the need to agree to license &etc. terms.)"
    echo " (So, download from website manually and install the .dmg file.)"
    echo "Once you've done this..."
    echo "Press any key to continue..."
    # as of 2017-05-08, this is: ????.dmg
    # ref: https://superuser.com/questions/689315/run-safari-from-terminal-with-given-url-address-without-open-command
    # ref: https://www.macissues.com/2014/09/18/how-to-launch-and-quit-applications-in-os-x-using-the-terminal/
    /Applications/Safari.app/Contents/MacOS/Safari & sleep 1 && osascript -e 'tell application "Safari" to open location "https://developer.apple.com/xcode/"'
    #echo "* Install .dmg"
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    # Enable commandline tools: in terminal
    xcode-select --install
    # Install homebrew (must be administrator): in terminal
    sudo ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"
    # Add homebrew to path: in terminal
    echo `export PATH="/usr/local/bin:$PATH"` >> ~/.bash_profile
    source ~/.bash_profile # bash
    brew tap caskroom/cask
    # Install git: in terminal
    brew install git
    # Install unique ID library: in terminal
    brew install ossp-uuid
    # Install Boost library and configure it in a fresh shell: in terminal
    brew install boost
    echo 'export BOOST_ROOT=/usr/local' >> ~/.bash_profile
    source ~/.bash_profile # bash
    # Install pip3: in terminal
    brew install python3
    curl -O https://bootstrap.pypa.io/get-pip.py
    sudo -H python3 get-pip.py
    # Install ninja build system: in terminal
    brew install cmake
    brew install pkg-config
    sudo -H pip3 install scikit-build
    sudo -H pip3 install ninja
    # Install meson build configuration: in terminal
    sudo -H pip3 install meson==0.42.1
    # Install python plotting capabilities (optional): in terminal
    sudo -H pip3 install matplotlib
    sudo -H pip3 install pandas
    # Install Oracle JDK
    brew cask install java
    # Install ant for command line build of java programs
    brew install ant
    echo "Dependencies installed!"
    
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then

    echo "Installing Prerequisite Tools on Ubuntu Linux"
    # run an 'apt update' check without sudo
    # ref: https://askubuntu.com/questions/391983/software-updates-from-terminal-without-sudo
    aptdcon --refresh
    NUMBER_UPGRADEABLE=`apt-get -s upgrade | grep "upgraded," | cut -d' ' -f1`
    if [ $NUMBER_UPGRADEABLE -gt 0 ]
    then
        echo "Some packages require updating, running apt update-upgrade as sudo now..."
        sudo apt -y update
        sudo apt -y upgrade
        echo "Done with apt update-upgrade!"
    fi

    # Install pkg-config for finding link arguments: in terminal
    sudo apt -y install pkg-config
    # Install git: in terminal
    sudo apt -y install git
    sudo apt -y install gitk
    # Install opengl development headers: in terminal
    sudo apt -y install libglu1-mesa-dev
    # Install unique ID creation library: in terminal
    sudo apt -y install uuid-dev
    # Install Boost libraries (**optional but recommended**; see external dependencies section): in terminal
    sudo apt-get -y install libboost-filesystem-dev libboost-regex-dev libboost-system-dev
    # Install pip3: in terminal
    sudo apt -y install python3-pip
    sudo -H pip3 install --upgrade pip
    # Install ninja build system: in terminal
    sudo -H pip3 install ninja
    # Install meson build configuration: in terminal
    sudo -H pip3 install meson==0.42.1
    # Install python plotting capabilities (optional): in terminal
    sudo apt -y install python3-tk
    sudo -H pip3 install matplotlib
    sudo -H pip3 install pandas
    # Install Java
    sudo apt -y install openjdk-11-jdk
    # Install ant for command line build of java programs
    sudo apt -y install ant
    echo "Dependencies installed!"

else
    echo "Unsupported platform! Only Ubuntu Linux and Mac OSX supported"
    exit 1
fi

echo "Configuring UxAS"
#check to see if already in OpenUxAS
current_directory=${PWD##*/}
git_directory=$PWD'/.git'
if [ $current_directory != "OpenUxAS" ] || [ ! -d $git_directory ]; then
    echo "Checking out OpenUxAS ..."
    git clone -b develop --single-branch https://github.com/afrl-rq/OpenUxAS.git
fi

# ensure one directory above OpenUxAS
if [ $current_directory == "OpenUxAS" ] && [ -d $git_directory ]; then
   cd ..
fi

if [ ! -d LmcpGen ]; then
	echo "Checking out LmcpGen ..."
	git clone https://github.com/afrl-rq/LmcpGen.git
fi
cd LmcpGen
ant -q jar
cd ..

if [ ! -d OpenAMASE ]; then
	echo "Checkout out OpenAMASE..."
	git clone https://github.com/afrl-rq/OpenAMASE.git
fi
cd OpenAMASE/OpenAMASE
ant -q jar
cd ../..
  
echo "Configuring UxAS plotting utilities ..."
cd OpenUxAS/src/Utilities/localcoords
sudo python3 setup.py install
cd ../../..

echo "Preparing UxAS build ..."
rm -rf build build_debug
python3 prepare
sh RunLmcpGen.sh
meson build --buildtype=release
meson build_debug --buildtype=debug

echo "Performing initial UxAS build ..."
ninja -C build
ninja -C build_release

cat <<'EOF'

================================================================

DONE!

Subsequent builds are done using:

  $ ninja -C build_debug

and 

  $ ninja -C build
EOF

# --eof--
