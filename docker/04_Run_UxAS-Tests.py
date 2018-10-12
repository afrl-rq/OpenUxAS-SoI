#! /usr/bin/env python3

import os
from subprocess import call 

hostOpenUxAS_Dir = '{0}/..'.format(os.getcwd())

print("\n##### START uxas_build container #####\n")
cmd = ('docker run -i --rm ' +
      '--name uxas_run_tests -w="/UxASDev/OpenUxAS" ' +
      '--mount type=bind,source={0}/..,target="/UxASDev" '.format(hostOpenUxAS_Dir) +
      '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
      'uxas/uxas-build:x86_64 ' +
      'python/usr/bin/python3 /UxASDev/OpenUxAS/docker/ContainerScriptsAndFiles/runUxAS_tests.py')
call(cmd,shell=True)
