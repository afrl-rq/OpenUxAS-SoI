#! /usr/bin/env python3

import sys
import os
from pathlib import Path
from subprocess import call 
import time
import json

timeStartAll = time.time()

uxasDir = Path(Path.cwd()).parent.name
hostOpenUxAS_Dir = '{0}/..'.format(os.getcwd())


print("\n##### STARTING DOCKER BUILD #####\n")
sys.stdout.flush()

call('export PATH=/usr/local/bin:$PATH',shell=True)

print("\n##### START uxas_build container #####\n")
sys.stdout.flush()

cmd = ('docker run -i --rm -d ' +
      '--name uxas_build -w="/UxASDev/{0}" '.format(uxasDir) +
      '--mount type=bind,source={0}/../..,target="/UxASDev" '.format(os.getcwd()) +
      '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
      'uxas/uxas-build:x86_64')
call(cmd,shell=True)


timeStartBuild = time.time()
print("\n##### START BuildUxAS #####\n")
sys.stdout.flush()
cmd = 'docker exec -i uxas_build  /usr/bin/python3 /UxASDev/{0}/docker/ContainerScriptsAndFiles/buildUxAS.py {0}'.format(uxasDir)
call(cmd,shell=True)
print('\n##### FINISHED-BuildUxAS  Build Time [{0}] #####\n\n\n'.format(time.time() - timeStartBuild))
sys.stdout.flush()
print('\n##### KILL uxas_build container #####\n')
sys.stdout.flush()
cmd = 'docker kill uxas_build'
call(cmd,shell=True)

print("\n#####  Building Deploy Container #####\n\n\n")
sys.stdout.flush()
cmd = 'docker build -t uxas/uxas-deploy:x86_64 -f ContainerScriptsAndFiles/Dockerfile_uxas-deploy .'
call(cmd,shell=True)

print('\n##### FINISHED  Total Build/Deploy Time [{0}] #####\n'.format(time.time() - timeStartAll))
sys.stdout.flush()


