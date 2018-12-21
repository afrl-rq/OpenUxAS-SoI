#! /usr/bin/env python3

import os
from pathlib import Path
from subprocess import call 

docker_Dir = Path(Path.cwd()).parent.name
hostOpenUxAS_Dir = '{0}/..'.format(os.getcwd())

print("\n##### START uxas_build container #####\n")
cmd = ('docker run -i --rm -d ' +
      '--name uxas_build ' +
      '--mount type=bind,source={0}/..,target="/UxASDev" '.format(hostOpenUxAS_Dir) +
      '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
      '-w="/UxASDev/{}" '.format(docker_Dir) +
      'uxas/uxas-build:x86_64 ')
call(cmd,shell=True)

cmd = "docker exec -i uxas_build bash -c  _UXAS_DIR={0}/".format(docker_Dir)
call(cmd,shell=True)
cmd = 'docker exec -i uxas_build  /usr/bin/python3 /UxASDev/{0}/docker/ContainerScriptsAndFiles/runPrepare_RunLmcpGen.py {0}'.format(docker_Dir)
call(cmd,shell=True)

cmd = 'docker kill uxas_build'
call(cmd,shell=True)
