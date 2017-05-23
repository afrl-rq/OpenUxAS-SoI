#!/bin/bash -e
# Copyright (c) 2017, by University of Cincinnati
# All rights reserved.
# Additional copyright may be held by others, as reflected in the commit history.
# 
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 
# 1. Redistributions of source code must retain the above copyright
# notice, this list of conditions and the following disclaimer.
# 
# 2. Redistributions in binary form must reproduce the above copyright
# notice, this list of conditions and the following disclaimer in the
# documentation and/or other materials provided with the distribution.
# 
# 3. Neither the name of the University of Cincinnati nor
# the names of its contributors may be used to endorse or promote
# products derived from this software without specific prior
# written permission.
# 
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
# FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL CALTECH
# OR THE CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
# USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
# OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
# SUCH DAMAGE.

# there is some cleaner stuff we can do here between scripts that we are enacting now
#
# basically, if we run something as "source my_script.sh" or ". ./myscript.sh",
# then it is run at the same "level" as the calling shell (or script) and changes are
# persistent, e.g.,
# -- "source" the subscript in a top-level script for the subscript to see all the
#    environment variables in that script
# -- modify an environment variable in the subscript for the top-level script that
#    "source"d it to see the change in the top-level script
#
# if you only want to share a few env vars from the top-level down, and make
# no changes to the env vars above:
# -- "export" a environment variable in the top-level script for the subscript to see
#    only that environment variable
# -- do not "source" the subscript for changes in the subscript not to affect the
#    top-level script
# see: http://stackoverflow.com/questions/9772036/pass-all-variables-from-one-shellscript-to-another

echo "Start of get_dlvsco_wd_f.sh script!"
echo "(sets DOWNLOAD_VS_COMPILE, WORKSPACEDIR, FORCE environment variable for a script 'source'ing it)"
echo "input arguments: DOWNLOAD_VS_COMPILE [WORKSPACEDIR] [-f]"
echo "(note: optional input arguments in [])"
echo "(note: there is no default DOWNLOAD_VS_COMPILE. Acceptable inputs are: -h --help -d -c)"
echo "(      -h, --help = show help text only and then exit script)"
echo "(      -d = download jar files, -c = compile jar files via NetBeans projects)"
echo "(note: default [WORKSPACEDIR] is \"~/UxAS_pulls\")"
echo "WORKSPACEDIR must specify the absolute path of the directory"
echo "-f sets FORCE=-f and will force a (re)install of all compiled-from-source components."

# note:
# source'ing this script overwrites $0 -- in other words, the call of the script itself

#
# INPUT ARGUMENT PARSING:
#

# set defaults for input arguments
DOWNLOAD_VS_COMPILE=
WORKSPACEDIR="/home/$USER/UxAS_pulls"
FORCE=
# if we get an input parameter (username) then use it, else use default 'vagrant'
# get -f (force) if given
if [ $# -lt 1 ]; then
    echo "ERROR: No switch specifying download (-d) vs. compile (-c) given as commandline argument. Exiting."
    exit
else # at least 1 (possibly 4) argument(s) at commandline...
    echo "Commandline argument 1 is: $1"
    if [ "$1" == "-h" ] || [ "$1" == "--help" ]; then # early exit
        echo "Descriptive-text-only requested."
        echo "Exiting."
        exit 1
    elif [ "$1" == "-d" ] || [ "$1" == "-c" ]; then # download jar files (-d) or compile jar files (-c)
        DOWNLOAD_VS_COMPILE=$1
    else
        echo "ERROR: Unknown switch given as commandline argument."
        echo "Currently, this script supports -h or --help (early exit), -d (download .jar files). -c (compile jar files) only."
        echo "Exiting."
        exit -1
    fi
    echo "Switch given is $DOWNLOAD_VS_COMPILE."
    if [ $# -lt 2 ]; then
        echo "Workspace directory not given as commandline argument. Using default of '$WORKSPACEDIR'."
    else # at least 2 (possibly more) arguments at commandline...
        if [ "$2" == "-f" ]; then # -f is last argument at commandline...
            echo "-f (force) commandline argument given."
            FORCE=$2
            echo "Default workspace directory path will be used."
        else # WORKSPACEDIR should be argument #2
            # but we need to / should check against the users that have home directories / can log in
            WORKSPACEDIR=$2
            if [ $# -gt 2 ] && [ "$3" == "-f" ]; then # at least 3 (possibly more) arguments at commandline...
                echo "-f (force) commandline argument given."
                FORCE=$3
            fi
        fi
    fi
fi
echo "Will be setting up UxAS workspace under $WORKSPACEDIR..."
if [ "$FORCE" == "-f" ]; then
    echo "Forcing install of all compiled-from-source components."
fi

echo "End of get_dlvsco_wd_f.sh script!"
