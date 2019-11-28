Building Uxas
=============

Common prerequisites
--------------------

You need to ensure that you have:

* Git installed
* Cmake
* C++ compiler
* pkg-config
* libuuid (uuid-dev package on ubuntu or debian)
* Ada compiler (to build ada demo)
* A Python 3.x

For note the build system will pick the compiler on the path. If you change the compiler
in the path a full rebuild will be triggered.

Bootstrapping your environment
------------------------------

In order to bootstrap your environment you need to perform the following commands:

$ ./install_env
$ . ./setup_env

Note: if the default python in your path is a python 2.x you may have to do explicitely:

$ python3 ./install_env

This step can be done only once. It will do the following:

* Check your environment for the prerequisites
* Create in 'vpython' subdirectory a python 3.x virtualenv with the necessary modules
  to launch anod-build command (see next section).

Building the project and its dependencies
-----------------------------------------

launch ./anod-build <target>

where target can be:

* uxas: to build the C++ uxas executable
* uxas-ada: to build the Ada demo
* amase: to build the simulator

Other targets are available to build some of the dependencies:

* lmcpgen: to build lmcpgen
* uxas-lmcp: will generate sources and build them for a given language.
    To select the language (ada, cpp, java, py), add the switch --qualifier=lang=<LANG>

Directory structure
-------------------

./README.txt         This file.
./anod-build         This the tool to build any spec present in the specs
                     subdirectory. You can use --help switch to see available
		     options
./install_env        Create the Python 3.x environment necessary to launch
                     anod-build
./setup_env          Source that script to put the Python environment in your PATH
./specs/*.anod       The build specifications for the different component of UxAS
./specs/config/repositories.yaml
                     Configuration file containing the list of repositories used
./specs/patches/*.patch
                     Contain some local patches for some corresponding anod specs
./sbx                The sandbox in which everything is build. You will find a directory
                     <platform>/<name> for each component built. These directories are
	             called 'build space's (generated)
./vpython            The python environment to run anod-build (generated)

Each build space usually have the following subdirectories:

./src                Location in which sources are installed
./build              Directory in which the build is performed
./install            Directory in which a component is installed

Repositories Used
-----------------

The list of repositories used is in specs/config/repositories.yaml. The file is configured
so that local openuxas sources are used. For all other repositories an automatic checkout 
is done. In case you want to manage a given checkout you can change the repositories.yaml
file. For example if you want to control the lmcpgen sources, replace:

    lmcpgen:
        vcs: git
        url: git@github.com:AdaCore/LmcpGen.git
        revision: ada

By:

   
    lmcpgen:
        vcs: external
        url: /some_absolute_dir_containing_your_checkout
        revision: None

In that case the build script will pick the content of your directory instead of doing an
automatic checkout. In that case the script do not try to do updates.

Force rebuild
-------------

If you pass --force to uxas-build command, current state will be ignore and
everything rebuilt from scratch
