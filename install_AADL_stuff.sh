#!/bin/bash
# Copyright © 2017 Government of the United States of America, as represented by the Secretary of the Air Force.
# No copyright is claimed in the United States under Title 17, U. S. Code. All Other Rights Reserved.
# Copyright 2017 University of Cincinnati. All rights reserved. See LICENSE.md file at:
# https://github.com/afrl-rq/OpenUxAS
# Additional copyright may be held by others, as reflected in the commit history.

# from Tool_Installation_and_Setup_Instructions.docx, 2017-05-24:
# For the most-updated instructions, see:
# -- https://github.com/afrl-rq/OpenUxAS/tree/architecture/AADL_project/doc

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
elif [ "$(expr substr $(uname -s) 1 10)" == "MINGW32_NT" ]; then # Win32
    echo "Sorry, native Windows (32-bit) O/S is currently unsupported by this script."
    exit 1
elif [ "$(expr substr $(uname -s) 1 10)" == "MINGW64_NT" ]; then # Win64
    echo "Sorry, native Windows (64-bit) O/S is currently unsupported by this script."
    exit 1
else
    echo "I don't know -what- this platform is ('$(expr substr $(uname -s) 1 10)'?) -- unsupported!"
    exit 1
fi

#
# starting 'installation' process
#

if [ "$(uname)" == "Darwin" ]; then
#if [ "$($(uname -s) | cut -c 1-6)" == "Darwin" ]; then

    mkdir -p ~/osate2-2.2.2

    echo "Install Prerequisites on Mac OS X"
    echo " "
    # Install homebrew (must be administrator): in terminal
    sudo ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"
    # Add homebrew to path: in terminal
    echo `export PATH="/usr/local/bin:$PATH"` >> ~/.bash_profile
    source ~/.bash_profile # bash
    # Install wget tar unzip sed -- only if you want the GNU versions of these tools, installs to /usr/local/bin
    #brew install coreutils # call by gwget, gtar...
    # unzip-to-7za: https://superuser.com/questions/626721/trying-to-unzip-file
    #brew install p7zip # call via 7za x file.zip
    #brew install gnu-sed # call by gsed
    # Install Oracle Java run-time (required for LmcpGen)
    # grab the .dmg file from: https://java.com/en/download/manual.jsp
    wget -O jre-XXXXX-macosx-x64.dmg http://javadl.oracle.com/webapps/download/AutoDL?BundleId=220306_d54c1d3a095b4ff2b6607d096fa80163
    # as of 2017-05-08, this is: jre-8u131-macosx-x64.dmg
    # command modified from: http://stackoverflow.com/questions/22934083/install-dmg-package-on-mac-os-from-terminal
    MOUNTDIR=$(echo `hdiutil mount jre-XXXXX-macosx-x64.dmg | tail -1 | awk '{$1=$2=""; print $0}'` | xargs -0 echo) && sudo installer -pkg "${MOUNTDIR}/"*.pkg -target / 
    echo "Installing OSATE 2.2.2..."
    cd ~/osate2-2.2.2
    wget -O osate2-2.2.2-vfinal-linux.gtk.x86_64.tar.gz http://aadl.info/aadl/osate/stable/2.2.2/products/osate2-2.2.2-vfinal-linux.gtk.x86_64.tar.gz
    tar -xvzf osate2-2.2.2-vfinal-linux.gtk.x86_64.tar.gz
    echo "Running OSATE2, v.2.2.2..."
    echo "* Choose a workspace, then press 'OK'."
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    ./osate &
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Install the Z3 Plugin inside OSATE2 (used by AGREE)"
    echo "* Select 'Help'->'Install New Software...'"
    echo "* In the 'Work with:' field, type the following, then hit enter:"
    echo "https://raw.githubusercontent.com/smaccm/update-site/master/site.xml"
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Check tool versions used / plugin installation..."
    echo "* Select 'Help'->'Installation Details'"
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Set OSATE Preferences for AGREE..."
    echo "* Select 'Window'->'Preferences', then 'Agree'->'Analysis'"
    echo "* In the Analysis panel, under 'Agree Analysis Settings':"
    echo "  * 'Model Checker Setting' should be JKind"
    echo "  * 'SMT Solver' should be Z3"
    echo "  * Set 'Maximum Number of PDR Instances' to '2' if 4+ CPU cores, '1' otherwise"
    echo "  * Uncheck 'Generate inductive counterexamples'"
    echo "  * Click 'Apply' to save settings"
    echo "* Click 'OK' to exit Preferences window"
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Import the UxAS AADL Project..."
    echo "* Select 'File'->'Import', then 'General'->'Existing Projects into Workspace'"
    echo "* Click 'Next'"
    echo "* In the Import popup window:"
    echo "  * 'Select root directory:' should be the ./OpenUxAS/AADL_project directory, so browse"
    echo "    to the directory and then click 'OK'"
    echo "    (e.g., if you used the default OpenUxAS workspace directory in ./checkout_plus_config.sh,"
    echo "     then in another window you're going to need to swap branches first, via:"
    echo "     cd /home/$USER/UxAS_pulls/OpenUxAS && git checkout architecture"
    echo "     and then the project's root directory will be: /home/$USER/UxAS_pulls/OpenUxAS/AADL_project )"
    echo "  * Under 'Projects:', make sure that the 'UxAS' box is checked"
    echo "  * Click 'Finish' to exit the Import window"
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    
    echo "...Congratulations! You're done with the installation and setup!"

elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then

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
    sudo apt -y install firefox wget tar unzip sed
    
    mkdir -p /home/$USER/osate2-2.2.2

    echo "Installing Prerequisite Tools on Ubuntu Linux (/ ...Bash on Ubuntu on Windows?)"
    # Install Oracle Java run-time (required for LmcpGen): in terminal
    echo " "
    sudo add-apt-repository ppa:webupd8team/java
    sudo apt update; sudo apt -y install oracle-java8-installer
    sudo apt -y install oracle-java8-set-default
    
    echo "Installing OSATE2 2.2.2..."
    cd /home/$USER/osate2-2.2.2
    wget -O osate2-2.2.2-vfinal-linux.gtk.x86_64.tar.gz http://aadl.info/aadl/osate/stable/2.2.2/products/osate2-2.2.2-vfinal-linux.gtk.x86_64.tar.gz
    tar -xvzf osate2-2.2.2-vfinal-linux.gtk.x86_64.tar.gz
    if [ "`lsb_release -sc`" == "xenial" ]; then # fix the Eclipse vs. Ubuntu 16.04 issue
        # note that installing the plugin from the interface doesn't seem to work in Ubuntu 16.04, out of the box
        # is a problem with eclipse + Ubuntu 16.04:
        # ref: https://stackoverflow.com/questions/36822242/eclipse-doesnt-work-with-ubuntu-16-04
        # add at line 3 of osate.ini (the equivalent of eclipse.ini):
        #line 2: plugins/org.eclipse.equinox.launcher_1.3.100.v20150511-1540.jar
        #line 3: --launcher.GTK_version
        #line 4: 2
        #line 5: --launcher.library
        sed -i.orig '3s/--launcher.library/--launcher.GTK_version\n2\n--launcher.library/' osate.ini
    fi
    echo "Running OSATE2, v.2.2.2..."
    echo "* Choose a workspace, check 'Use this as the default and do not ask again', then press 'OK'."
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    ./osate &
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Install the Z3 Plugin inside OSATE2 (used by AGREE)"
    echo "* Select 'Help'->'Install New Software...'"
    echo "* In the 'Work with:' field, type the following, then hit enter:"
    echo "https://raw.githubusercontent.com/smaccm/update-site/master/site.xml"
    echo "* Wait for the list to load, then open out 'SMACCM' and check the 'Z3 Plugin' box"
    echo "* Click 'Next', click 'Next' to confirm, accept the license agreement terms, click 'Finish'"
    echo "* In the 'Security Warning' dialogue box, click 'OK'"
    echo "* Click 'Yes' to restart OSATE2"
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Check tool versions used / plugin installation..."
    echo "* Select 'Help'->'Installation Details'"
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Set OSATE Preferences for AGREE..."
    echo "* Select 'Window'->'Preferences', then 'Agree'->'Analysis'"
    echo "* In the Analysis panel, under 'Agree Analysis Settings':"
    echo "  * 'Model Checker Setting' should be JKind"
    echo "  * 'SMT Solver' should be Z3"
    echo "  * Set 'Maximum Number of PDR Instances' to '2' if 4+ CPU cores, '1' otherwise"
    echo "  * Uncheck 'Generate inductive counterexamples'"
    echo "  * Click 'Apply' to save settings"
    echo "* Click 'OK' to exit Preferences window"
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    echo "Import the UxAS AADL Project..."
    echo "* Select 'File'->'Import', then 'General'->'Existing Projects into Workspace'"
    echo "* Click 'Next'"
    echo "* In the Import popup window:"
    echo "  * 'Select root directory:' should be the ./OpenUxAS/AADL_project directory, so browse"
    echo "    to the directory and then click 'OK'"
    echo "    (e.g., if you used the default OpenUxAS workspace directory in ./checkout_plus_config.sh,"
    echo "     then in another window you're going to need to swap branches first, via:"
    echo "     cd /home/$USER/UxAS_pulls/OpenUxAS && git checkout architecture"
    echo "     and then the project's root directory will be: /home/$USER/UxAS_pulls/OpenUxAS/AADL_project )"
    echo "  * Under 'Projects:', make sure that the 'UxAS' box is checked"
    echo "  * Click 'Finish' to exit the Import window"
    echo "Once you're done..."
    echo "Press any key to continue..." # reference: https://ss64.com/bash/read.html
    read -rs -p " " -n 1 # reference: https://ss64.com/bash/read.html
    echo " "
    
    #
    # installing Z3 from source:
    # * https://github.com/Z3Prover/z3
    # * https://github.com/Z3Prover/z3/wiki/Documentation
    #
    # 32-bit Ubuntu 14.04:
    ##cd /home/$USER/initdeps
    ##wget https://github.com/Z3Prover/z3/releases/download/z3-4.5.0/z3-4.5.0-x86-ubuntu-14.04.zip
    ##unzip z3-4.5.0-x86-ubuntu-14.04.zip
    # 64-bit Ubuntu 14.04:
    #cd /home/$USER/initdeps
    ##wget https://github.com/Z3Prover/z3/releases/download/z3-4.5.0/z3-4.5.0-x64-ubuntu-14.04.zip
    ##unzip z3-4.5.0-x64-ubuntu-14.04.zip
    ## -versus-
    #git clone https://github.com/Z3Prover/z3.git
    #cd z3
    #python scripts/mk_make.py --java
    #cd build
    #make
    #sudo make install
    ##sudo make uninstall
    
    # see: https://github.com/smaccm/update-site
    # and: https://github.com/smaccm/update-site/blob/master/site.xml
    # which led to: http://aadl.info/aadl/osate/testing/update-site/
    # alternately: http://aadl.info/aadl/osate/stable/2.2.2/update-site/
    
    echo "...Congratulations! You're done with the installation and setup!"

#elif [ "$(expr substr $(uname -s) 1 10)" == "MINGW32_NT" ]; then # Win32
    
#    mkdir C:\AADL_stuff
#    wget http://aadl.info/aadl/osate/stable/2.2.2/products/osate2-2.2.2-vfinal-win32.win32.x86.zip
#    unzip osate2-2.2.2-vfinal-win32.win32.x86.zip
    
#elif [ "$(expr substr $(uname -s) 1 10)" == "MINGW64_NT" ]; then # Win64

#    mkdir C:\AADL_stuff
#    wget http://aadl.info/aadl/osate/stable/2.2.2/products/osate2-2.2.2-vfinal-win32.win32.x86_64.zip
#    unzip osate2-2.2.2-vfinal-win32.win32.x86_64.zip
    
fi

echo "All done with script 'install_AADL_stuff.sh'!"

# --eof--
