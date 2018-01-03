This directory include two sub-directories, "develop" and "deploy".

The files in the "develop" directory are used to build a Docker image
	containing all of the UxAS prerequsite software which is then used to
	build UxAS and run the UxAS tests on the host computer.

The files in the "deploy" directory are used to build a Docker image
	that includes the UxAS binary and the libraries required at run-time.
	That image is then used to run UxAS in a direcory mounted from the
	host computer.