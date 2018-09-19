#! /usr/bin/env python3

import os
from subprocess import call 

hostOpenUxAS_Dir = '{0}/..'.format(os.getcwd())

print("\n##### START removing build files #####\n")
cmd = ('docker run --rm -d ' +
      '--name uxas_build -w="/UxASDev/OpenUxAS" ' +
      '--mount type=bind,source={0}/..,target="/UxASDev" '.format(hostOpenUxAS_Dir) +
      '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
      'uxas/uxas-build:x86_64 ' +
      'rm -rf /tmp_build/build_debug')
call(cmd,shell=True)
