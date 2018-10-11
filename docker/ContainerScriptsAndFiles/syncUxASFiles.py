#! /usr/bin/env python3
import time
import os
from subprocess import call 

def callWithShell(cmd):
    call(cmd,shell=True)

timeStartAll = time.time()

print("\n#### SYNCING FILES ####\n")

callWithShell("rsync -rt /UxASDev/OpenUxAS/meson_options.txt /tmp_build/meson_options.txt")
callWithShell("rsync -rt /UxASDev/OpenUxAS/meson.build /tmp_build/meson.build")
callWithShell("rsync -rt /UxASDev/OpenUxAS/3rd/ /tmp_build/3rd")
callWithShell("rsync -rt /UxASDev/OpenUxAS/resources/ /tmp_build/resources")
callWithShell("rsync -rt /UxASDev/OpenUxAS/src/ /tmp_build/src")
callWithShell("rsync -rt /UxASDev/OpenUxAS/tests/ /tmp_build/tests")

if(os.path.isdir("/UxASDev/OpenUxAS/UxAS-afrl_internal")):
    callWithShell("mkdir -p /tmp_build/UxAS-afrl_internal")
    callWithShell("rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/meson.build /tmp_build/UxAS-afrl_internal/meson.build")
    callWithShell("rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/odroid-cross.txt /tmp_build/UxAS-afrl_internal/odroid-cross.txt")
    callWithShell("rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/3rd/ /tmp_build/UxAS-afrl_internal/3rd")
    callWithShell("rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/resources/ /tmp_build/UxAS-afrl_internal/resources")
    callWithShell("rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/src/ /tmp_build/UxAS-afrl_internal/src")
    callWithShell("rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/tests/ /tmp_build/UxAS-afrl_internal/tests")

print("\n#### FINISHED-SYNCING FILES [{0}] ####\n".format(time.time() - timeStartAll))


