#!/bin/bash
#This is the automated cratous running script
#This is to be used to test multiple instances of ICAROUS communicating with one instance of UxAS

TEMPVAR=$(pwd)

cd /dev/mqueue
rm -r ./*
cd $TEMPVAR

cd /home/nia-visi8/UxAS_pulls/OpenUxAS/examples/12_Live_Demo_3/

./runAMASE_Live_Demo_3.sh&

sleep 3

gnome-terminal --command "sh -c 'echo; cd /home/nia-visi8/UxAS_pulls/OpenUxAS/examples/12_Live_Demo_3/; ./runUxAS_Live_Demo_1.sh; exec bash'"

sleep 2

gnome-terminal --command "sh -c 'echo; cd /home/nia-visi8/ICAROUS_pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"

sleep 4

gnome-terminal --command "sh -c 'echo; cd /home/nia-visi8/ICAROUS_pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"

sleep 4

gnome-terminal --command "sh -c 'echo; cd /home/nia-visi8/ICAROUS_pulls/icarous/cFS/bin/cpu1/ && ./core-cpu1; exec bash'"
