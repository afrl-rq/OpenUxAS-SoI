###### Introduction #########

The realtime_middleware/gams_service branch differs from the main branch
in that we have added services based on open source projects in addition
to the contents of the main branch in order to provide real-time and quality-
of-service properties in the UxAS services. As we're adding features, we're
also adding a moderate amount of new software dependencies. This README
attempts to address these installation requirements so new users can use
the contents of this branch quickly.

####### Pre-requisites ######

Install everything mentioned in the README.md file for UxAS. We do not
remove software dependencies. We add to them.

####### New installations ###

1. GAMS and MADARA with tests (leave off tests if you don't want tests). Copy
   and paste the following, after you have modified GAMS_ROOT to be an
   appropriate location on your harddrive (e.g., $HOME/software/gams).

     export GAMS_ROOT=<wherever you want GAMS to go>
     git clone -b master --single-branch https://github.com/jredmondson/gams $GAMS_ROOT
     $GAMS_ROOT/scripts/linux/base_build.sh prereqs ace madara gams vrep tests

   Copy the export= printouts to the bottom of your .bashrc and .profile files
   in your home directory ($HOME/.bashrc) and ($HOME/.profile) and then reload
   your terminal or source those files in an existing terminal with:

     source $HOME/.bashrc

   If you want to test the installation, see if you can call:

     $MADARA_ROOT/bin/karl -h

   You should see a help menu displayed for the KaRL interpreter. For more
   information and troubleshooting, please see the installation Wiki page
   for GAMS here: https://github.com/jredmondson/gams/wiki/GAMS-Installation#linux-build-scripts

2. DART dmplc compiler. This branch also includes support for the DART dmplc
   formally verifying compiler project. The instructions for installing DART
   dmplc are the following:

     cd $HOME
     git clone --depth 1 -b release-0.4.0 https://github.com/cps-sei/dmplc.git

     export DMPL_ROOT=$HOME/dmplc
     export PATH=$DMPL_ROOT/src/dmplc:$PATH
     export PATH=$DMPL_ROOT/src/vrep:$PATH

     cd $DMPL_ROOT
     make clean
     make MZSRM=0

   As with the GAMS/MADARA installation, it is advised that you update your
   .bashrc and .profile files with DMPL_ROOT and also add $DMPL_ROOT/src/dmplc
   to your $PATH variable.


