#!/bin/bash
#This is the automated cratous running script
#This is to be used to test multiple instances of ICAROUS communicating with one instance of UxAS

TEMPVAR=$(pwd)

cd /dev/mqueue
rm -r ./*
cd $TEMPVAR

cd $HOME/UxAS_pulls/OpenUxAS/examples/12_Live_Demo_3/



./runAMASE_Live_Demo_3.sh&

sleep 3

gnome-terminal --geometry=74x19+-10+14 --command "sh -c 'echo; cd ${HOME}/UxAS_pulls/OpenUxAS/examples/12_Live_Demo_3/; ./runUxAS_Live_Demo_3.sh; exec bash'"

sleep 2

gnome-terminal --geometry=74x19--5+14 --command "sh -c 'echo; cd ${HOME}/ICAROUS_pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"

sleep 4

gnome-terminal --geometry=74x19--5-29 --command "sh -c 'echo; cd ${HOME}/ICAROUS_pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"

sleep 4

gnome-terminal --geometry=74x19+-10-29 --command "sh -c 'echo; cd ${HOME}/ICAROUS_pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"
