#! /usr/bin/env python3

# This script starts a 'samba' server that connects to a given docker volume
# making it possible to browse the volume

import os
from subprocess import call 

dockerVolume = 'UxAS_Build_Vol'

print('SET_UP A FOLDER FOR SAMBA TO SERVE')
cmd = ('docker run -it --rm -v {0}:/workdir  busybox chown -R 1000:1000 /workdir'.format(dockerVolume))
call(cmd,shell=True)

print('Create and run THE SAMBA container')
print('This container is what will allow you to see the files in the volume.')
cmd = ('docker create -t -p 445:445 --name samba -v {0}:/workdir crops/samba'.format(dockerVolume))
call(cmd,shell=True)

#####################################################
#OSX
print('Create an alias for 127.0.0.1')
print('OSX will not let you connect to a locally running samba share. Therefore, create an alias for 127.0.0.1 of 127.0.0.2.')
print('Since you will always need to have the alias to connect to the samba container, ')
print(' you could also combine the start of samba and alias like so:')
cmd = ('docker start samba && sudo ifconfig lo0 127.0.0.2 alias up')
call(cmd,shell=True)

print('Open Finder, then hit "Command-K". In the "Server Address" box type smb://127.0.0.2/workdir and click "Connect". Log in as guest.')
