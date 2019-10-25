Building Uxas
=============

Common prerequisites
--------------------

You need to ensure that you have:

* Git installed
* Cmake
* C++ compiler
* Ada compiler (to build ada demo)
* Java (oracle version)
* Python with e3-core package installed
  (pick the e3transition branch from https://github.com/AdaCore/e3-core)

If you are part of AdaCore, you can run the following script to install the
C++/Ada compiler, a suitable version of python (that contains e3-core) and 
Java 10.x from Oracle.

  $ ./install_env   # (only once)
  $ . ./setup_env   # will put java 10.x, the compiler and python in the PATH

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
