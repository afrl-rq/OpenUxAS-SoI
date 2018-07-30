#!/bin/bash
#This is the automated cratous running script
#This is to be used to test multiple instances of ICAROUS communicating with one instance of UxAS

TEMPVAR=$(pwd)

#This is to remove the 
cd /dev/mqueue
rm -r ./*
cd $TEMPVAR

#Demo number goes here [1-3]
DEMO="1"

if [ $USER = "nia" ]
then
    #This is for Winston's directory structure
    cd $HOME/uxas-pulls/OpenUxAS/examples/12_Live_Demo_${DEMO}/

    ./runAMASE_Live_Demo_${DEMO}.sh&

    sleep 3
    gnome-terminal --geometry=74x19+-10+14 --command "sh -c 'echo; cd ${HOME}/uxas-pulls/OpenUxAS/examples/12_Live_Demo_${DEMO}/; ./runUxAS_Live_Demo_${DEMO}.sh; exec bash'"

    sleep 2
    gnome-terminal --geometry=74x19--5+14 --command "sh -c 'echo; cd ${HOME}/icarous-pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"

    sleep 4
    gnome-terminal --geometry=74x19--5-29 --command "sh -c 'echo; cd ${HOME}/icarous-pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"

    sleep 4
    gnome-terminal --geometry=74x19+-10-29 --command "sh -c 'echo; cd ${HOME}/icarous-pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"
    #End of Winston's
else
    #This is for Paul's directory structure
    cd $HOME/UxAS_pulls/OpenUxAS/examples/12_Live_Demo_${DEMO}/

    ./runAMASE_Live_Demo_${DEMO}.sh&

    sleep 3
    gnome-terminal --geometry=74x19+-10+14 --command "sh -c 'echo; cd ${HOME}/UxAS_pulls/OpenUxAS/examples/12_Live_Demo_${DEMO}/; ./runUxAS_Live_Demo_${DEMO}.sh; exec bash'"

    sleep 2
    gnome-terminal --geometry=74x19--5+14 --command "sh -c 'echo; cd ${HOME}/ICAROUS_pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"

    sleep 4
    gnome-terminal --geometry=74x19--5-29 --command "sh -c 'echo; cd ${HOME}/ICAROUS_pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"

    sleep 4
    gnome-terminal --geometry=74x19+-10-29 --command "sh -c 'echo; cd ${HOME}/ICAROUS_pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"
    #End of Paul's
fi
