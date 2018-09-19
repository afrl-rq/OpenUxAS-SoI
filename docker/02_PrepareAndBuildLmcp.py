#! /usr/bin/env python3

import os
from subprocess import call 

hostOpenUxAS_Dir = '{0}/..'.format(os.getcwd())

print("\n##### START uxas_build container #####\n")
cmd = ('docker run -i --rm -d ' +
      '--name uxas_build ' +
      '--mount type=bind,source={0}/..,target="/UxASDev" '.format(hostOpenUxAS_Dir) +
      '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
      '-w="/UxASDev/OpenUxAS" ' +
      'uxas/uxas-build:x86_64 ')
call(cmd,shell=True)

cmd = 'docker exec -i uxas_build  /usr/bin/python3 /UxASDev/OpenUxAS/docker/ContainerScriptsAndFiles/runPrepare_RunLmcpGen.py'
call(cmd,shell=True)

cmd = 'docker kill uxas_build'
call(cmd,shell=True)
