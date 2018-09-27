#! /usr/bin/env python3
import os
from subprocess import call 
import platform

containerName = 'uxas_helloworld'
cfgFile = 'cfg_HelloWorld.xml'

osType = platform.system()
print('** osType[{}] **'.format(osType))
if osType =='Linux':
      pass
elif osType =='Darwin':
      pass
elif osType =='Windows':
      pass

print('\n** Starting Container[{0}] **\n'.format(containerName))
cmd = 'docker run -i --rm --name {0} -w="/working" --mount type=bind,source={1},target="/working"  uxas/uxas-deploy:x86_64 -cfgPath {2}'.format(containerName,os.getcwd(),cfgFile)
call(cmd,shell=True)
print('\n** Container[{0}] Stopped and Removed **'.format(containerName))


