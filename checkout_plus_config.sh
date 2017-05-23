#!/bin/bash -e
# Copyright © 2017 Government of the United States of America, as represented by the Secretary of the Air Force.
# No copyright is claimed in the United States under Title 17, U. S. Code. All Other Rights Reserved.
# Copyright 2017 University of Cincinnati. All rights reserved. See LICENSE.md file at:
# https://github.com/afrl-rq/OpenUxAS
# Additional copyright may be held by others, as reflected in the commit history.

# from the README.md, 2017-05-23:

# references for Darwin vs. Linux if-elif-fi:
# * http://stackoverflow.com/questions/3466166/how-to-check-if-running-in-cygwin-mac-or-linux/17072017#17072017
# * https://serverfault.com/questions/501230/can-not-seem-to-get-expr-substr-to-work
# references for Safari call to open webbrowser:
# https://superuser.com/questions/689315/run-safari-from-terminal-with-given-url-address-without-open-command
# ref: https://www.macissues.com/2014/09/18/how-to-launch-and-quit-applications-in-os-x-using-the-terminal/

# making sure we exit the script early if we're on an unsupported O/S:
if [ "$(uname)" == "Darwin" ]; then
#if [ "$($(uname -s) | cut -c 1-6)" == "Darwin" ]; then
    : # do nothing
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    : # do nothing
else
    echo "This is a Windows platform (Cygwin?) -- unsupported!"
    exit 1
fi

#
# find path of this-script-being-run
# see: http://stackoverflow.com/questions/630372/determine-the-path-of-the-executing-bash-script
#
RELATIVE_PATH="`dirname \"$0\"`"
ABSOLUTE_PATH="`( cd \"$RELATIVE_PATH\" && pwd )`"
echo "PATH of current script ($0) is: $ABSOLUTE_PATH"

#
# parse input vars (set to appropriate vars or default vars)
#
echo "Commandline arguments are: '$@'"
source $ABSOLUTE_PATH/get_dlvsco_wd_f.sh "$@"
# when source'd, sets these vars at this level: DOWNLOAD_VS_COMPILE WORKSPACEDIR FORCE
echo "Switches are: DOWNLOAD_VS_COMPILE='$DOWNLOAD_VS_COMPILE', WORKSPACEDIR='$WORKSPACEDIR', FORCE='$FORCE'..."
echo " "

# change these arguments if you want to get your repositories from a different fork
REPO_SOURCE_OU=afrl-rq 
REPO_SOURCE_OA=afrl-rq
REPO_SOURCE_LG=afrl-rq
if [ "$DOWNLOAD_VS_COMPILE" == "-d" ]; then
    echo "Grabbing jar files from:"
elif [ "$DOWNLOAD_VS_COMPILE" == "-c" ]; then
    echo "Grabbing source code from:"
else
    echo "Bad switch for DOWNLOAD_VS_COMPILE(=$DOWNLOAD_VS_COMPILE), exiting."
    exit -1
fi
echo "* $REPO_SOURCE_OU"
echo "* $REPO_SOURCE_OA"
echo "* $REPO_SOURCE_LG"
echo " "

#
# starting 'checkout + configuration + compilation' process
#

if [ "$FORCE" == "-f" ]; then
    echo "Force switch active, removing UxAS subdirectories from ~/UxAS_pulls prior to build..."
    rm -rf $WORKSPACEDIR/OpenUxAS
    rm -rf $WORKSPACEDIR/OpesAMASE
    rm -rf $WORKSPACEDIR/LmcpGen
fi

mkdir -p $WORKSPACEDIR
cd $WORKSPACEDIR
echo "Grabbing the main UxAS codeset (OpenUxAS)"
git clone https://github.com/$REPO_SOURCE_OU/OpenUxAS.git

if [ "$DOWNLOAD_VS_COMPILE" == "-d" ]; then
    echo "Download OpenAMASE:"
    mkdir -p $WORKSPACEDIR/OpenAMASE/OpenAMASE/dist
    echo "Please log into your github account in the webbroswer."
    echo "(You will see a 404 error at first, but once you've logged in, the download should automatically start.)"
    echo "Then save the file (OpenAMASE.jar) to $WORKSPACEDIR/OpenAMASE/OpenAMASE/dist"
    #echo "(If you'd rather compile from source instead, then just close the browser tab and continue.)"
    echo "Once you're done..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    if [ "$(uname)" == "Darwin" ]; then
    #if [ "$($(uname -s) | cut -c 1-6)" == "Darwin" ]; then
        /Applications/Safari.app/Contents/MacOS/Safari & sleep 1 && osascript -e 'tell application "Safari" to open location "https://github.com/$REPO_SOURCE_OA/OpenAMASE/releases/download/v1.0.0/OpenAMASE.jar"'
    elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
        firefox https://github.com/$REPO_SOURCE_OA/OpenAMASE/releases/download/v1.0.0/OpenAMASE.jar &
    fi
    echo " "
elif [ "$DOWNLOAD_VS_COMPILE" == "-c" ]; then
    cd $WORKSPACEDIR
    echo "Checkout + compile OpenAMASE:"
    git clone https://github.com/$REPO_SOURCE_OA/OpenAMASE.git
    echo "Loading provided Netbeans project for compile..."
    #echo "If you didn't download the OpenAMASE.jar file, then:"
    echo "Please click 'Build' inside the project."
    echo "Once you're done..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    cd $WORKSPACEDIR/OpenAMASE/OpenAMASE
    if [ "$(uname)" == "Darwin" ]; then
    #if [ "$($(uname -s) | cut -c 1-6)" == "Darwin" ]; then
        # command modified from: http://stackoverflow.com/questions/1272920/run-terminal-command-on-startup-of-netbeans-in-mac-osx
        /Applications/NetBeans/NetBeans.app/MacOS/Contents/NetBeans nbproject # or `open -a NetBeans.app`
    elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
        #echo "  /bin/sh \"/usr/local/netbeans-7.4/bin/netbeans\" &"  # if sudo install
        ~/netbeans-8.2/bin/netbeans nbproject & # if non-sudo install
    fi
    echo " "
fi

if [ "$DOWNLOAD_VS_COMPILE" == "-d" ]; then
    cd $WORKSPACEDIR
    echo "Download LmcpGen:"
    mkdir -p $WORKSPACEDIR/LmcpGen/dist
    echo "Please log into your github account in the webbroswer."
    echo "(You will see a 404 error at first, but once you've logged in, the download should automatically start.)"
    echo "Then save the file (LmcpGen.jar) to $WORKSPACEDIR/LmcpGen/dist"
    echo "(If you'd rather compile from source instead, then just close the browser tab and continue.)"
    echo "Once you're done..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    if [ "$(uname)" == "Darwin" ]; then
    #if [ "$($(uname -s) | cut -c 1-6)" == "Darwin" ]; then
        /Applications/Safari.app/Contents/MacOS/Safari & sleep 1 && osascript -e 'tell application "Safari" to open location "https://github.com/$REPO_SOURCE_LG/LmcpGen/releases/download/v1.1.0/LmcpGen.jar"'
    elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
        firefox https://github.com/$REPO_SOURCE_LG/LmcpGen/releases/download/v1.1.0/LmcpGen.jar &
    fi
    echo " "
elif [ "$DOWNLOAD_VS_COMPILE" == "-c" ]; then
    cd $WORKSPACEDIR
    echo "Checkout + compile LmcpGen:"
    git clone https://github.com/$REPO_SOURCE_LG/LmcpGen.git
    echo "Loading provided Netbeans project for compile..."
    echo "If you didn't download the LmcpGen.jar file, then:"
    echo "Please click 'Build' inside the project."
    echo "Once you're done..."
    read -rs -p "Press any key to continue..." -n 1 # reference: https://ss64.com/bash/read.html
    cd $WORKSPACEDIR/LmcpGen
    if [ "$(uname)" == "Darwin" ]; then
    #if [ "$($(uname -s) | cut -c 1-6)" == "Darwin" ]; then
        # command modified from: http://stackoverflow.com/questions/1272920/run-terminal-command-on-startup-of-netbeans-in-mac-osx
        /Applications/NetBeans/NetBeans.app/MacOS/Contents/NetBeans nbproject # or `open -a NetBeans.app`
    elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
        #echo "  /bin/sh \"/usr/local/netbeans-7.4/bin/netbeans\" &"  # if sudo install
        ~/netbeans-8.2/bin/netbeans nbproject & # if non-sudo install
    fi
    echo " "
fi

echo "Auto-generating source code for LMCP libraries..."
cd $WORKSPACEDIR/OpenUxAS
# this assumes that in the file system, LmcpGen is at the same level as OpenUxAS
sh RunLmcpGen.sh
echo "Preparing UxAS specific patches to external libraries..."
./prepare
echo "*** Note that ./prepare will need to be run again any time a file is modified in one of the /3rd/wrap_patches subdirectories or the /3rd/*.wrap.tmpl files, or any time you move or rename your source tree. ***"

cd $WORKSPACEDIR/OpenUxAS
echo "Performing first build of OpenUxAS..."
echo "(This step need only be done once.)"
meson build --buildtype=release
meson build_debug --buildtype=debug

# this step requires OpenAMASE directory to exist at same level as OpenUxAS in the local filesystem
# thus, it comes at the end of everything else
cd $WORKSPACEDIR/OpenUxAS/src/Utilities/localcoords
echo "Add python package for UxAS plotting (for OpenAMASE)"
sudo -H python3 setup.py install

echo "...Congratulations! You're done with the 'checkout + configuration + compilation' step!"

echo " "
echo "To build UxAS, try typing:"
echo "cd $WORKSPACEDIR/OpenUxAS"
echo "ninja -C build all"
echo " "
echo "To run UxAS tests, try typing:"
echo "cd $WORKSPACEDIR/OpenUxAS"
echo "ninja -C build test"
echo " "
echo "To run specific UxAS tests, try looking at:"
echo "gedit $WORKSPACEDIR/OpenUxAS/examples/02_Example_WaterwaySearch/README.md &"
echo "gedit $WORKSPACEDIR/OpenUxAS/examples/03_Example_DistributedCooperation/README.md &"
echo " "
echo "To refresh external dependencies, try typing:"
echo "cd $WORKSPACEDIR/OpenUxAS"
echo "./rm-external"
echo "./prepare"
echo " "

echo "All done with script 'checkout_plus_config.sh'!"

# --eof--
