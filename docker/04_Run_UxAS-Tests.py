#! /usr/bin/env python3

import os
from pathlib import Path
from subprocess import call 

uxasDir = Path(Path.cwd()).parent.name
hostOpenUxAS_Dir = '{0}/..'.format(os.getcwd())

print("\n##### START uxas_build container #####\n")
cmd = ('docker run -i --rm ' +
      '--name uxas_run_tests -w="/UxASDev/{0}" '.format(uxasDir) +
      '--mount type=bind,source={0}/..,target="/UxASDev" '.format(hostOpenUxAS_Dir) +
      '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
      'uxas/uxas-build:x86_64 ' +
      '/usr/bin/python3 /UxASDev/{0}/docker/ContainerScriptsAndFiles/runUxAS_tests.py'.format(uxasDir))
call(cmd,shell=True)
