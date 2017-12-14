The files in this directory are used to construct
and deploy a Docker container that is used to build
UxAS.

FILES:

01_buildImage_UxAS_build.sh - this is a linux script that 
	uses Docker commands to construct the "uxas/build" 
	Docker image

Dockerfile.UxAS_build - this is the DockerFile that defines
	the "uxas/build" Docker image 

02_buildUxAS_WithDocker.sh - this is a linux script that
	utilizes the "uxas/build" Docker container to build UxAS

buildUxAS.sh - this is a linux script that calls meson
	and ninja from inside the "uxas/build" Docker image

03_stopAndRemoveBuildContainer.sh - this is a linux script
	that uses docker commands to stop and remove the 
	"uxas/build" Docker container


InstallLibraries - the files in this directory are used
	to install UxAS prequisites that require installation
	from source code
