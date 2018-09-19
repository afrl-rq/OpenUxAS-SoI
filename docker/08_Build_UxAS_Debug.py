#! /usr/bin/env python3

import os
from subprocess import call 
import time

timeStartAll = time.time()

hostOpenUxAS_Dir = '{0}/..'.format(os.getcwd())


print("\n##### STARTING DOCKER DEBUG BUILD #####\n")

call('export PATH=/usr/local/bin:$PATH',shell=True)

timeStartBuild = time.time()

print("\n##### START uxas_build_debug container #####\n")
cmd = ('docker run -i --rm -d ' +
      '--name uxas_build_debug -w="/UxASDev/OpenUxAS" ' +
      '--mount type=bind,source={0}/../..,target="/UxASDev" '.format(os.getcwd()) +
      '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
      'uxas/uxas-build:x86_64')
call(cmd,shell=True)

timeStartBuild = time.time()
print("\n##### START BuildUxAS #####\n")
cmd = 'docker exec -i uxas_build_debug  bash /UxASDev/OpenUxAS/docker/ContainerScriptsAndFiles/buildUxAS_Debug.sh'
call(cmd,shell=True)
print('\n##### FINISHED-BuildUxAS  Build Time [{0}] #####\n\n\n'.format(time.time() - timeStartBuild))

print('\n##### KILL uxas_build_debug container #####\n')
cmd = 'docker kill uxas_build_debug'
call(cmd,shell=True)



# docker run -it --rm -w="/UxASDev/OpenUxAS" --mount source=UxAS_Build_Vol,target="/tmp_build" uxas/uxas-build:x86_64
# docker run -i --rm --name uxas_build -w="/UxASDev/OpenUxAS" --mount source=UxAS_Build_Vol,target="/tmp_build" uxas/uxas-build:x86_64


