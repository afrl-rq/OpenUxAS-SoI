#! /usr/bin/env python3


import os
from subprocess import call 
import time

timeStartAll = time.time()

print("\n##### STARTING- to construct BUILD image #####\n")
cmd = 'docker build -t uxas/uxas-build:x86_64 -f ContainerScriptsAndFiles/Dockerfile_uxas-build .'
returned_value = call(cmd,shell=True); print('returned value:{0}'.format(returned_value))
print('\n##### FINISHED-constructing BUILD image Time [{0}] #####\n\n\n'.format(time.time() - timeStartAll))
