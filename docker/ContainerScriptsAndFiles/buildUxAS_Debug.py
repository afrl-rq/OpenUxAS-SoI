#! /usr/bin/env python3
import time
import sys
import os
import subprocess
from subprocess import call 

def callWithShell(cmd):
    process = subprocess.Popen(cmd,shell=True)
    process.wait()
    
if len(sys.argv) > 1:
    	uxasDir = sys.argv[1]
else:
	uxasDir = 'OpenUxas'

startAllTime = time.time()


print("\n*** Sync Files ### \n")
sys.stdout.flush()
callWithShell("python /UxASDev/{0}/docker/ContainerScriptsAndFiles/syncUxASFiles.py {0}".format(uxasDir))

print( "\n#### RUNNING MESON ####\n")
sys.stdout.flush()

startMeson = time.time()

# 1 - change to the directory: 
os.chdir("/tmp_build")

# 2
# if "build" exists the just run Ninja
if(not os.path.isdir("build_debug")):
    callWithShell("meson build_debug --buildtype=debug")

print( "\n#### FINISHED RUNNING MESON [{}] ####\n.".format(time.time() - startMeson))
sys.stdout.flush()

print("\n#### RUNNING NINJA ####\n")
sys.stdout.flush()

ninjaStart = time.time()

# 3 - compile the code

callWithShell("ninja -C build_debug uxas")

print("\n#### FINISHED RUNNING NINJA [{}] ####\n".format(time.time() - ninjaStart))
sys.stdout.flush()
callWithShell("mkdir -p /UxASDev/{0}/docker/tmp/debug".format(uxasDir))

callWithShell("cp /tmp_build/build_debug/uxas /UxASDev/{0}/docker/tmp/debug/uxas".format(uxasDir))

print( "\n#### FINISHED! Total Time [{}] ####\n".format(time.time() - startAllTime))
sys.stdout.flush()
