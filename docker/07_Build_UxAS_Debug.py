#! /usr/bin/env python3

import os
from pathlib import Path
from subprocess import call 
import time

timeStartAll = time.time()

uxasDir = Path(Path.cwd()).parent.name
hostOpenUxAS_Dir = '{0}/..'.format(os.getcwd())


print("\n##### STARTING DOCKER DEBUG BUILD #####\n")

call('export PATH=/usr/local/bin:$PATH',shell=True)

timeStartBuild = time.time()

print("\n##### START uxas_build_debug container #####\n")
cmd = ('docker run -i --rm -d ' +
      '--name uxas_build_debug -w="/UxASDev/{0}" '.format(uxasDir) +
      '--mount type=bind,source={0}/../..,target="/UxASDev" '.format(os.getcwd()) +
      '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
      'uxas/uxas-build:x86_64')
call(cmd,shell=True)

timeStartBuild = time.time()
print("\n##### START BuildUxAS #####\n")
cmd = 'docker exec -i uxas_build_debug  /usr/bin/python3 /UxASDev/{0}/docker/ContainerScriptsAndFiles/buildUxAS_Debug.py {0}'.format(uxasDir)
call(cmd,shell=True)
print('\n##### FINISHED-BuildUxAS  Build Time [{0}] #####\n\n\n'.format(time.time() - timeStartBuild))

print('\n##### KILL uxas_build_debug container #####\n')
cmd = 'docker kill uxas_build_debug'
call(cmd,shell=True)



# cmd = 'docker run -it --rm -w="/UxASDev/{0}" --mount source=UxAS_Build_Vol,target="/tmp_build" uxas/uxas-build:x86_64'.format(uxasDir)
# cmd = 'docker run -i --rm --name uxas_build -w="/UxASDev/{0}" --mount source=UxAS_Build_Vol,target="/tmp_build" uxas/uxas-build:x86_64'.format(uxasDir)


