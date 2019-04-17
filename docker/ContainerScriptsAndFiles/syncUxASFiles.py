#! /usr/bin/env python3
import time
import os
import sys
from subprocess import call 

def callWithShell(cmd):
    #print(cmd)
    call(cmd,shell=True)

if len(sys.argv) > 1:
    uxasDir = sys.argv[1]
else:
	uxasDir = 'OpenUxas'
    		

timeStartAll = time.time()

print("\n#### SYNCING FILES ####\n")

callWithShell("rsync -rt /UxASDev/{0}/meson_options.txt /tmp_build/meson_options.txt".format(uxasDir))
callWithShell("rsync -rt /UxASDev/{0}/meson.build /tmp_build/meson.build".format(uxasDir))
callWithShell("rsync -rt /UxASDev/{0}/3rd/ /tmp_build/3rd".format(uxasDir))
callWithShell("rsync -rt /UxASDev/{0}/resources/ /tmp_build/resources".format(uxasDir))
callWithShell("rsync -rt /UxASDev/{0}/src/ /tmp_build/src".format(uxasDir))
callWithShell("rsync -rt /UxASDev/{0}/tests/ /tmp_build/tests".format(uxasDir))

if(os.path.isdir("/UxASDev/{0}/UxAS-afrl_internal".format(uxasDir))):
    callWithShell("mkdir -p /tmp_build/UxAS-afrl_internal".format(uxasDir))
    callWithShell("rsync -rt /UxASDev/{0}/UxAS-afrl_internal/meson.build /tmp_build/UxAS-afrl_internal/meson.build".format(uxasDir))
    callWithShell("rsync -rt /UxASDev/{0}/UxAS-afrl_internal/odroid-cross.txt /tmp_build/UxAS-afrl_internal/odroid-cross.txt".format(uxasDir))
    callWithShell("rsync -rt /UxASDev/{0}/UxAS-afrl_internal/3rd/ /tmp_build/UxAS-afrl_internal/3rd".format(uxasDir))
    callWithShell("rsync -rt /UxASDev/{0}/UxAS-afrl_internal/resources/ /tmp_build/UxAS-afrl_internal/resources".format(uxasDir))
    callWithShell("rsync -rt /UxASDev/{0}/UxAS-afrl_internal/src/ /tmp_build/UxAS-afrl_internal/src".format(uxasDir))
    callWithShell("rsync -rt /UxASDev/{0}/UxAS-afrl_internal/tests/ /tmp_build/UxAS-afrl_internal/tests".format(uxasDir))

print("\n#### FINISHED-SYNCING FILES [{0}] ####\n".format(time.time() - timeStartAll))


