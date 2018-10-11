#! /usr/bin/env python3

import os
from subprocess import call 

print("\n##### START uxas_build container #####\n")
cmd = ('docker run -i --rm ' +
      '--name uxas_run -w="/working" ' +
      '--mount type=bind,source="{}",target="/working" '.format(os.getcwd()) +
      'uxas/uxas-deploy:x86_64 ' +
      '-cfgPath ./cfg_TestUxAS.xml')
call(cmd,shell=True)

