#! /usr/bin/env python3

import os
from subprocess import call 

# print("\n##### START uxas_build container #####\n")
cmd = ('docker run -i --rm --privileged -p 8298:8298 ' +
      '--name uxas_test_debug -w="/working" ' +
      '--mount type=bind,source="{}",target="/working" '.format(os.getcwd()) +
      '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
      'uxas/uxas-build:x86_64 ' + 
      'gdbserver host:8298 /tmp_build/build_debug/uxas -cfgPath ./cfg_TestUxAS.xml')
call(cmd,shell=True)


# print("\n##### START uxas_build container interactive #####\n")
# cmd = ('docker run -it --rm --privileged -p 8298:8298 ' +
#       '--name uxas_test_debug -w="/working" ' +
#       '--mount type=bind,source="{}",target="/working" '.format(os.getcwd()) +
#       '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
#       'uxas/uxas-build:x86_64 ')
# call(cmd,shell=True)

# print("\n##### START uxas_build_debug container interactive #####\n")
# cmd = ('docker run -it --rm  --privileged ' +
#       '--name uxas_debug -w="/working" ' +
#       '--mount type=bind,source="{}",target="/working" '.format(os.getcwd()) +
#       '--mount source=UxAS_Build_Vol,target="/tmp_build" ' + 
#       'uxas/uxas-build:x86_64')
# call(cmd,shell=True)



# configure cross gdb
#../../gdb-8.1/configure --prefix=/opt/gdb/x86_64-linux-gnu/cross --target=x86_64-linux-gnu
#make
#make install

# run cross gdb
# /opt/gdb/x86_64-linux-gnu/cross/bin/x86_64-linux-gnu-gdb ../tmp/debug/uxas 
# (gdb) target remote :8298