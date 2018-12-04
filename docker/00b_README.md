** UxAS in Docker **
* Updated - `7/16/2018`


# Overview
The files in this directory are used to construct and deploy Docker
container images that are used to build and deploy UxAS. The build 
image is intended to be self-contained; once built or downloaded, a 
network connection is not necessary to build the UxAS source tree.

# Quickstart

## Prerequisites
`Docker` - [https://docs.docker.com]
`Python`
`Internet Connection`

## Before Building UxAS
LmcpGen must be cloned into the same directory as this repository
(OpenUxAS). OpenAMASE can also be cloned as a sibling of OpenUxAS and
LmcpGen, but is optional. The directory structure should look like this:

* `/`
  * `LmcpGen/`
  * `OpenAMASE/` (optional)
  * `OpenUxAS/`

(optional, not recommended) construct the `uxas-build` Docker image:
	`python 99_construct_uxas-build.py`

1) `prepare` the `3rd` libraries, build and run LMCPGen:
	`python 01_PrepareAndBuildLmcp.py`
2) build UxAS and construct the `uxas-deploy` image:
	`python 02_BuildDeploy_UxAS.py`
3) the directory `03_test` contains a script and configuration file to test run the containerized UxAS

## Running UxAS in a Docker container can be accompilshed with the following command:
>docker run \
>  -i --rm \
>  --name uxas_run -w="/working" \
>  --mount type=bind,source="${PWD}",target="/working"\
>  uxas/uxas-deploy:x86_64 \
>  -cfgPath ./cfg_TestUxAS.xml

`run` - create a container and execute it
`-i` - run interactively
`--rm` - remove the container when it is stopped
`--name` - name of the container
`-w` - create a working directory in the container
`--mount` - mounts the current host directory to the container's `/working/` directory
`uxas/uxas-deploy:x86_64` - create a container from this image
`-cfgPath ./cfg_TestUxAS.xml` - configuration file to pass to UxAS

[https://docs.docker.com/engine/reference/run/]


# Docker Infrastructure

## IMPORTANT
Execution of UxAS in docker on different operating systems can change
the implementation details. Please read the file `00c_README_OS_Differences.md`
for specifics on these details.


### Directory contents
  -- NOTE: .py are python scripts

- `99_construct_uxas-build.py` uses Docker commands to construct the
  `uxas-build` Docker image.

- `01_PrepareAndBuildLmcp.py` uses the `uxas-build` Docker image
  to run `prepare` and `RunLmcpGen.sh` commands.

- `02_BuildDeploy_UxAS.py` uses the `uxas-build` Docker image
  to build UxAS and construct a `uxas-deploy` Docker image.

- `03_test` folder containg scripts to demonstrate how to run UxAS in
  the files in the directory are:
  	-- `01_Run_UxAS.py` starts UxAS in a `uxas-deploy` container 
   	-- `cfg_TestUxAS.xml` the configuration file used by UxAS.

- `04_runUxAS_Tests.py` runs the UxAS test suite within a `uxas-build`
  container.

- `05_RemoveBuildFiles.py` uses the `uxas-build` Docker image
  to remove the 'build' directory from the 'internal' Docker Volume.
  This will force `meson` to create a new build directory

- `06_RemoveSourceFilesInVolume.py`  uses the `uxas-build` Docker image
  to remove the 'source' directories from the 'internal' Docker Volume.
  This will force `rsync` to re-upload the source files.

- `07_Build_UxAS_Debug.py`  uses the `uxas-build` Docker image
  to build a `debug` version of UxAS which is stored in the Docker volume
  and copied into the directory, `OpenUxAS/tmp/debug/`.

- `09_test_debug` folder containg scripts to demonstrate how to start the
  the debug version of UxAS using `gdbserver`. The files in the directory
  are:
  	-- `01_Run_UxAS_Debug.py` starts `gdbserver`, with uxas as the target,
    in a `uxas-build` container. 
   	-- `cfg_TestUxAS.xml` the test configuration file used by UxAS.
  * NOTE: see `00d_README_Debugging.md` for information on debugging UxAS 
    in Docker containers.    


#### Container Scripts and Files
* NOTE: Along with the docker files that define the Docker images, the other 
files in the directory `OpenUxAS/docker/ContainerScriptsAndFiles` are scripts
that are designed to be executed inside the Docker containers.

- `buildUxAS_Debug.py` calls the appropriate Meson and Ninja from inside the
  `uxas-build` Docker image to build a debug version of UxAS.

- `buildUxAS.py` calls the appropriate Meson and Ninja from inside the
  `uxas-build` Docker image to build a release version of UxAS

- `Dockerfile_uxas-build` is the DockerFile that defines the
  `uxas-build` Docker image which contains all of the prerequisite
  necessary to build UxAS.

- `Dockerfile_uxas-deploy` is the DockerFile that defines the
  `uxas-deploy` Docker image which contains a UxAS executable and 
  any required shared libraries.

- 'getDependencies.sh' script used to copy all the all shared libraries 
  required by an executable to a given directory  

- `InstallLibraries` contains scripts for installing UxAS prequisites
  from source. Not meant to be used manually.

- `runUxAS_tests.py` calls the appropriate Meson and Ninja from inside the
  `uxas-build` Docker image to run the UxAS test suite . Not meant to be 
  used manually.

- `syncUxasFiles.py` is used to synchronize the UxAS source files, that is,
  if any files are different in the source directories than in the Docker 
  volume, rsync copies the souce file to the volume.    


## Details

The Docker infrastructure for x86_64 uses Ubuntu 17.10 as a base
image, and then installs development tools and libraries needed
to build and test UxAS (the `develop` image). Another image installs
only the shared libraries required by the resulting executable, in
order to make a deployment as small as possible (the `deploy` image).

### Ubuntu

Ubuntu is currently used as a base because it has historically been a
supported platform for UxAS. However, this may change in the future to
a distribution like Alpine Linux in order to reduce the size of
deployment images.

### Self-Contained

While the basic UxAS build system can use Meson wrap dependencies to
satisfy most of its third party requirements, the `develop` image
provides those dependencies in the usual system locations (e.g.,
`/usr/lib` and `/usr/local/lib`). This means that the `develop` image
can build UxAS from start to finish without a network connection.

### Owned By Root

The main rough edge with the Docker infrastructure is the need to use
`sudo` to clean up after it.

The scripts in this directory often invoke Docker with a local disk
mount option so that local development is reflected in the build
container, and so that the build process does not have to start from a
fresh Meson build directory for each Docker-based build.

Since the user within the Docker container is `root` by default, the
files touched during the build therefore become owned by `root`, which
is not what one expects to see in their build tree. You can run `sudo
chown -R youruser:yourgroup` on your OpenUxAS directory, but we are
working on better options.
