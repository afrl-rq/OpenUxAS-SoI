#!/usr/bin/env bash
# Copyright © 2017 Government of the United States of America, as represented by the Secretary of the Air Force.
# No copyright is claimed in the United States under Title 17, U. S. Code. All Other Rights Reserved.
# Copyright 2017 University of Cincinnati. All rights reserved. See LICENSE.md file at:
# https://github.com/afrl-rq/OpenUxAS
# Additional copyright may be held by others, as reflected in the commit history.

# from the README.md, 2017-05-08:


# references:
# * http://stackoverflow.com/questions/3466166/how-to-check-if-running-in-cygwin-mac-or-linux/17072017#17072017
# * https://serverfault.com/questions/501230/can-not-seem-to-get-expr-substr-to-work

if [ "$(uname)" == "Darwin" ]; then
#if [ "$($(uname -s) | cut -c 1-6)" == "Darwin" ]; then

    echo "Install Prerequisites on Mac OS X"
    echo " "
    echo "Install XCode"
    echo "* Get yourself a developer account and grab the file from: https://developer.apple.com/xcode/"
    echo " (This cannot be downloaded automatically due to the need to agree to license &etc. terms.)"
    echo " (So, download from website manually and install the .dmg file.)"
    # as of 2017-05-08, this is: ????.dmg
    # ref: https://superuser.com/questions/689315/run-safari-from-terminal-with-given-url-address-without-open-command
    # ref: https://www.macissues.com/2014/09/18/how-to-launch-and-quit-applications-in-os-x-using-the-terminal/
    /Applications/Safari.app/Contents/MacOS/Safari & sleep 1 && osascript -e 'tell application "Safari" to open location "https://developer.apple.com/xcode/"'
    #echo "* Install .dmg"
    # command modified from: http://stackoverflow.com/questions/22934083/install-dmg-package-on-mac-os-from-terminal
    #MOUNTDIR=$(echo `hdiutil mount ???.dmg | tail -1 | awk '{$1=$2=""; print $0}'` | xargs -0 echo) && sudo installer -pkg "${MOUNTDIR}/"*.pkg -target / 
    echo "Once you've done this..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    # Enable commandline tools: in terminal
    xcode-select --install
    # Install homebrew (must be administrator): in terminal
    sudo ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"
    # Add homebrew to path: in terminal
    echo `export PATH="/usr/local/bin:$PATH"` >> ~/.bash_profile
    # Install git: in terminal
    brew install git
    # Install unique ID library: in terminal
    brew install ossp-uuid
    # Install doxygen and related packages (optional): in terminal
    brew install doxygen
    brew install graphviz
    brew cask install mactex
    # Install pip3: in terminal
    brew install python3
    # Install pip2: in terminal
    curl -O https://bootstrap.pypa.io/get-pip.py
    sudo -H python get-pip.py
    # Install ninja build system: in terminal
    brew install cmake
    brew install pkg-config
    sudo -H pip3 install scikit-build
    sudo -H pip3 install ninja
    # Install meson build configuration: in terminal
    sudo -H pip3 install meson
    # Install python plotting capabilities (optional): in terminal
    sudo -H pip2 install matplotlib
    sudo -H pip2 install pandas
    # Install Oracle Java run-time (required for LmcpGen)
    # grab the .dmg file from: https://java.com/en/download/manual.jsp
    wget -O jre-XXXXX-macosx-x64.dmg http://javadl.oracle.com/webapps/download/AutoDL?BundleId=220306_d54c1d3a095b4ff2b6607d096fa80163
    # as of 2017-05-08, this is: jre-8u131-macosx-x64.dmg
    # command modified from: http://stackoverflow.com/questions/22934083/install-dmg-package-on-mac-os-from-terminal
    MOUNTDIR=$(echo `hdiutil mount jre-XXXXX-macosx-x64.dmg | tail -1 | awk '{$1=$2=""; print $0}'` | xargs -0 echo) && sudo installer -pkg "${MOUNTDIR}/"*.pkg -target / 
    echo " "
    echo "Install Netbeans and Oracle Java JDK (optional)"
    # Download the Mac OSX version
    echo "* Grab the .dmg file from: http://www.oracle.com/technetwork/java/javase/downloads/jdk-netbeans-jsp-142931.html"
    echo " (This cannot be downloaded automatically due to the need to agree to license &etc. terms.)"
    echo " (So, download from website manually and install.)"
    # as of 2017-05-08, this is: jdk-8u131-nb-8_2-macosx-x64.dmg
    # ref: https://superuser.com/questions/689315/run-safari-from-terminal-with-given-url-address-without-open-command
    # ref: https://www.macissues.com/2014/09/18/how-to-launch-and-quit-applications-in-os-x-using-the-terminal/
    /Applications/Safari.app/Contents/MacOS/Safari & sleep 1 && osascript -e 'tell application "Safari" to open location "http://www.oracle.com/technetwork/java/javase/downloads/jdk-netbeans-jsp-142931.html"'    
#echo "* Install .dmg"
    # command modified from: http://stackoverflow.com/questions/22934083/install-dmg-package-on-mac-os-from-terminal
    #MOUNTDIR=$(echo `hdiutil mount jdk-8u131-nb-8_2-macosx-x64.dmg | tail -1 | awk '{$1=$2=""; print $0}'` | xargs -0 echo) && sudo installer -pkg "${MOUNTDIR}/"*.pkg -target / 
    echo "Once you've done this..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Enable C/C++ plug-in in Netbeans (optional)"
    echo "* Open Netbeans"
    echo "* Choose Tools->Plugins from the top menu"
    echo "* In the Available Plugins tab, search for C++"
    echo "* Select C/C++ and click Install"
    echo "Once you've done this..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    echo "...Congratulations! You're done with the dependencies installation!"
    
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then

    sudo apt update
    sudo apt install firefox

    echo "Installing Prerequisite Tools on Ubuntu Linux (/ ...Bash on Ubuntu on Windows?)"
    # Install git: in terminal
    sudo apt-get install git
    sudo apt-get install gitk
    # Install opengl development headers: in terminal
    sudo apt-get install libglu1-mesa-dev
    # Install unique ID creation library: in terminal
    sudo apt-get install uuid-dev
    # Install doxygen and related packages (optional): in terminal
    sudo apt-get install doxygen
    sudo apt-get install graphviz
    sudo apt-get install texlive
    # Install pip3: in terminal
    sudo apt install python3-pip
    sudo -H pip3 install --upgrade pip
    # Install pip2: in terminal
    sudo apt install python-pip
    # Install ninja build system: in terminal
    sudo -H pip3 install ninja
    # Install meson build configuration: in terminal
    sudo -H pip3 install meson
    # Install python plotting capabilities (optional): in terminal
    sudo apt install python-tk
    sudo -H pip2 install matplotlib
    sudo -H pip2 install pandas
    echo " "
    echo "Install Netbeans and Oracle Java JDK (optional)"
    # Download the Linux x64 version
    echo "* Grab the .sh file from: http://www.oracle.com/technetwork/java/javase/downloads/jdk-netbeans-jsp-142931.html"
    echo " (This cannot be downloaded automatically due to the need to agree to license &etc. terms.)"
    echo " (So, download from website manually to your ~/Downloads directory.)"
    # as of 2017-05-08, this is: jdk-8u131-nb-8_w-linux-x64.sh
    firefox http://www.oracle.com/technetwork/java/javase/downloads/jdk-netbeans-jsp-142931.html &
    echo "Once you've done this..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Running downloaded install script: in terminal"
    cd ~/Downloads; sh jdk-8u131-nb-8_w-linux-x64.sh
    echo "* Click Next three times, then Install"
    echo "Once you've done this..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Enable C/C++ plug-in in Netbeans (optional)"
    #echo "* Open Netbeans (in Ubuntu search, type Netbeans, or from commandline type:)"
    # command modified from: https://askubuntu.com/questions/440245/how-do-i-run-netbeans-from-the-terminal/440257#440257
    #echo "  /bin/sh \"/usr/local/netbeans-7.4/bin/netbeans\" &"  # if sudo install
    ~/netbeans-8.2/bin/netbeans & # if non-sudo install
    echo "* Choose Tools->Plugins from the top menu"
    echo "* In the Available Plugins tab, search for C++"
    echo "* Select C/C++ and click Install"
    echo "Once you've done this..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    # Install Oracle Java run-time (required for LmcpGen): in terminal
    sudo add-apt-repository ppa:webupd8team/java
    sudo apt update; sudo apt install oracle-java8-installer
    sudo apt install oracle-java8-set-default
    echo "...Congratulations! You're done with the dependencies installation!"

else
    echo "This is a Windows platform (Cygwin?) -- unsupported!"
    exit 1
fi


# --eof--
