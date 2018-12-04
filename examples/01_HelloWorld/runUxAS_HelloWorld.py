#! /usr/bin/env python3

import os
from subprocess import call 
import platform

osType = platform.system()
print('** osType[{}] **'.format(osType))

bin = '../../build/uxas'
cfgFile = 'cfg_HelloWorld.xml'
if osType =='Linux':
      pass
elif osType =='Darwin':
      pass
elif osType =='Windows':
      bin = '..\\..\\build\\uxas.exe'

cmd = '{0} -cfgPath {1}'.format(bin,cfgFile)
call(cmd,shell=True)
