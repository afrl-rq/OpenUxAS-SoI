The files in this directory are used to construct
and deploy Docker containers that are used to deploy
UxAS.

Notes: 
	1) UxAS must be built and the file: 'OpenUxAS/build/uxas' 
	must exist.

	2) The Docker image "steveras/uxas-run_deps:x86_64" must be 
	available on the local system or downloaded automatically
	from: the Docker Hub, "https://hub.docker.com/". 

FILES:

01_buildRun_Image.sh - this is a linux script that 
	uses Docker commands to construct the "uxas/run" 
	Docker image

02_runUxAS.sh - this is a linux script that uses the 
	"uxas/run" image to start UxAS in the local directory.

03_StopRunContainer.sh - this linux executes the docker command
	to stop the "uxas/run" container.

cfg_TestUxAS.xml - this is a sample UxAS configuration file.

Image/Dockerfile.UxAS_run - the DockerFile used to build the 
	"uxas/run" image.
