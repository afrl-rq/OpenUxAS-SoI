# ODROID-XU4 Cross Compilation

This directory contains a Dockerfile and scripts for building a Linux
image for the ODROID-XU4, and cross-compiling UxAS to that
environment.

## Before Building UxAS

LmcpGen must be cloned into the same directory as this repository
(OpenUxAS). OpenAMASE can also be cloned as a sibling of OpenUxAS and
LmcpGen, but is optional:

* `/`
  * `LmcpGen/`
  * `OpenAMASE/` (optional)
  * `OpenUxAS/`

## Build Steps

1. From the root of the OpenUxAS repository, run:
   `docker/odroidxu4/01_build_sdcard_and_sdk.sh`.

   This script uses Docker commands to construct the `uxas_cross`
   Docker image. The first time this image is built, Buildroot must be
   cloned and built in its entirety, which can take some
   time. However, subsequent runs will cache the results of that build
   step and be faster.
   
   If the upstream Buildroot repository changes, you will have to
   manually trigger a fetch by passing `-f` to the script:
   `docker/odroidxu4/01_build_sdcard_and_sdk.sh -f`.

2. From the root of the OpenUxAS repository, run:
   `docker/odroidxu4/02_cross_compile_uxas.sh`.

   This script uses the `uxas_cross` Docker image built in step 1 to
   cross-compile UxAS. The resulting binary will be found at
   `/OpenUxAS/build_cross/uxas`, ready to copy to the ODROID.
 
## Offline Builds

After running the first script, `01_build_sdcard_and_sdk.sh`, which
must be run with an internet connection, the OpenUxAS repository is
left in a state where the `02_cross_compile_uxas.sh` step can be run
without a connection.

However, this is somewhat fragile at the moment, as the `01` step
pre-fetches the 3rd party dependencies specified in Meson wrap
files. Running the `rm-external` script will therefore wipe out this
cached state, and a network connection will again be required to
proceed.
