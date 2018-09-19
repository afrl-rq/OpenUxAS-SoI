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

START_SYNC=$(timer)
printf "\n#### SYNCING FILES ####\n"
rsync -rt /UxASDev/OpenUxAS/meson_options.txt /tmp_build/meson_options.txt
rsync -rt /UxASDev/OpenUxAS/meson.build /tmp_build/meson.build
rsync -rt /UxASDev/OpenUxAS/3rd/ /tmp_build/3rd
rsync -rt /UxASDev/OpenUxAS/resources/ /tmp_build/resources
rsync -rt /UxASDev/OpenUxAS/src/ /tmp_build/src
rsync -rt /UxASDev/OpenUxAS/tests/ /tmp_build/tests

if [ -d "/UxASDev/OpenUxAS/UxAS-afrl_internal" ]; then 
	mkdir -p /tmp_build/UxAS-afrl_internal
	rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/meson.build /tmp_build/UxAS-afrl_internal/meson.build
	rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/odroid-cross.txt /tmp_build/UxAS-afrl_internal/odroid-cross.txt
	rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/3rd/ /tmp_build/UxAS-afrl_internal/3rd
	rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/resources/ /tmp_build/UxAS-afrl_internal/resources
	rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/src/ /tmp_build/UxAS-afrl_internal/src
	rsync -rt /UxASDev/OpenUxAS/UxAS-afrl_internal/tests/ /tmp_build/UxAS-afrl_internal/tests
fi


printf "\n#### FINISHED SYNCING FILES ["$(timer $START_SYNC)"] ####\n"


