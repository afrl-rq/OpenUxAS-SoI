#!/bin/bash -e

function timer()
{
    if [[ $# -eq 0 ]]; then
        echo $(date '+%s')
    else
        local  stime=$1
        etime=$(date '+%s')

        if [[ -z "$stime" ]]; then stime=$etime; fi

        dt=$((etime - stime))
        ds=$((dt % 60))
        dm=$(((dt / 60) % 60))
        dh=$((dt / 3600))
        printf '%d:%02d:%02d' $dh $dm $ds
    fi
}

START_ALL=$(timer)


printf "\n*** Sync Files ### \n"
bash /UxASDev/OpenUxAS/docker/ContainerScriptsAndFiles/syncUxasFiles.sh

printf "\n#### RUNNING MESON ####\n"
START=$(timer)

# 1 - change to the directory: OpenUxAS
cd /tmp_build


# 2
# if "build" exists the just run Ninja
if [ ! -d "build_debug" ]; then 
	echo "##### NEW MESON BUILD DIRECTORY #####"
	meson build_debug  --buildtype=debug
fi
printf "\n#### FINISHED RUNNING MESON ["$(timer $START)"] ####\n"

printf "\n#### RUNNING NINJA ####\n"
START=$(timer)

# 3 - compile the code
ninja -C build_debug all

printf "\n#### FINISHED RUNNING NINJA ["$(timer $START)"] ####\n"

mkdir -p /UxASDev/OpenUxAS/docker/tmp/debug
cp /tmp_build/build_debug/uxas /UxASDev/OpenUxAS/docker/tmp/debug/uxas

printf "\n#### FINISHED! Total Time ["$(timer $START_ALL)"] ####\n"


#/UxASDev/OpenUxAS/docker/develop/getDependencies.sh /tmp_build/build/uxas /tmp_build/RuntimeImage/

#ls -l /tmp_build/RuntimeImage/lib64





