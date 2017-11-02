Dependencies
============

The primary tools and dependencies to obtain, build, document, and
simulate UxAS are:

-   Git

-   OpenGL

-   UUID library

-   Boost

-   Python 3

-   Meson

-   Ninja

-   LmcpGen

-   OpenAMASE (optional, simulation)

-   NetBeans with Java JDK (optional, simulation)

-   Doxygen (optional, documentation)

-   LaTeX (optional, documentation)

The UxAS build system will download and compile the following external
libraries

-   Google Test (gTest)

-   ZeroMQ (zeromq, czmq, cppzmq, zyre)

-   SQLite

-   Zlib

-   Minizip

-   Serial

Libraries for XML and GPS message parsing have numerous forks without
centralized repository control. Code to build the following libraries is
included with UxAS.

-   PugiXML

-   TinyGPS

Supported platforms
===================

For an Ubuntu 16.04 or Mac OS X system with the listed prerequisite
tools installed, UxAS should build from source without issue. Support
for Windows is available on Windows 7 and 10 using Visual Studio.

Installing Prerequisite Tools on Ubuntu Linux -or- Mac OS X (Partially-Automated)
---------------------------------------------------------------------------------

The following is a bash script that helps to partially-automation the
“installing prerequisite tools” processes that are documented in this
README.md file below.

This has been tested-working on Ubuntu 16.04, as of 2017-05-23

1.  Download the script from the OpenUxAS repository
    (install\_most\_deps.sh) OR cd to your git clone d OpenUxAS
    directory

2.  Run the script at the terminal: ./install\_most\_deps.sh

3.  Follow the on-screen instructions

Note that the most up-to-date instructions on the dependencies-needed
for UxAS are available below.

Installing Prerequisite Tools on Ubuntu Linux
---------------------------------------------

1.  Install git: in terminal

    -   sudo apt-get install git

    -   sudo apt-get install gitk

2.  Install OpenGL development headers: in terminal

    -   sudo apt-get install libglu1-mesa-dev

3.  Install unique ID creation library: in terminal

    -   sudo apt-get install uuid-dev

4.  Install Boostlibraries (**optional but recommended**; see external
    dependencies section): in terminal

    -   sudo apt-get install libboost-filesystem-dev libboost-regex-dev
        libboost-system-dev

5.  Install doxygen and related packages **optional**: in terminal

    -   sudo apt-get install doxygen

    -   sudo apt-get install graphviz

    -   sudo apt-get install texlive

    -   sudo apt-get install texlive-latex-extra

6.  Install pip3: in terminal

    -   sudo apt install python3-pip

    -   sudo -H pip3 install –upgrade pip

7.  Install ninja build system: in terminal

    -   sudo -H pip3 install ninja

8.  Install meson build configuration: in terminal

    -   sudo -H pip3 install meson

9.  Ensure dependency search for meson is supported: in terminal

    -   sudo apt-get install pkg-config

10. Install python plotting capabilities (**optional**): in terminal

    -   sudo apt install python3-tk

    -   sudo -H pip3 install matplotlib

    -   sudo -H pip3 install pandas

11. Install NetBeans and Oracle Java JDK (**optional**)

    -   Download the Linux x64 version

    -   Run downloaded install script. In terminal: cd  Downloads; sh
        jdk-9u131-nb-8\_w-linux-x64.sh

    -   Click Next three times, then Install

12. Enable C/C++ plug-in in NetBeans (**optional**)

    -   Open NetBeans (in Ubuntu search, type NetBeans)

    -   Choose Tools-&gt;Plugins from the top menu

    -   In the Available Plugins tab, search for C++

    -   Select C/C++ and click Install

13. Install Oracle Java run-time (required from LmcpGen): in terminal

    -   sudo add-apt-repository ppa:webupd8team/java

    -   sudo apt update; sudo apt install oracle-java8-installer

    -   sudo apt install oracle-java8-set-default

Installing Prerequisites on Mac OS X
------------------------------------

1.  Install XCode

2.  Enable commandline tools. In terminal: xcode-select –install

3.  Install homebrew (must be administrator). In terminal: sudo ruby -e
    “\$(curl5 -fsSL
    https://raw.githubusercontent.com/Homebrew/install/master/install)”

4.  Add homebrew to path. In terminal: echo \$(export
    Path=“/usr/local/bin:\$PATH”) &gt;&gt;  /.bash\_profile

5.  Install git. In termin0al: brew install git

6.  Install unique ID library. In terminal: brew install ossp-uuid

7.  Install Boost library and configure it in a fresh shell. In
    terminal:

    -   brew install boost

    -   echo ’export BOOST\_ROOT=/usr/local’ &gt;&gt;  /.bash\_profile

    -   bash

8.  Install doxygen and related packages (**optional**). In terminal:

    -   brew install doxygen

    -   brew install graphviz

    -   brew cask install mactex

9.  Install pip3. In terminal:

    -   brew install python3

10. Install nonja build system. In terminal:

    -   brew install cmake

    -   brew install pkg-config

    -   sudo -H pip3 install scikit-build

    -   sudo -H pip3 install ninja

11. Install meson build configuration. In terminal:

    -   sudo -H pip3 install meson

12. Install python plotting capabilities (**optional**). In terminal:

    -   sudo -H pip3 install matplotlib

    -   sudo -H pip3 install pandas

13. Install Oracle Java run-time(required for LmcpGen)

14. Install NetBeans and Oracle JAva JDK (**optional**)

    -   Download the Mac OSX version

    -   Install .dmg

15. Enable C++ plug-in in NetBeans (**optional**)

    -   Open NetBeans

    -   Choose Tools-&gt;Plugins from the top menu

    -   In the Available Plugins tab, search for C++

    -   Select C/C++ and click Install

Prep and Build on Native Windows
--------------------------------

1. Install [Visual Studio 2017 Community Edition](https://www.visualstudio.com/downloads/)

    - Ensure C++ selected in `Workloads` tab

    - Ensure `Git for Windows` is selected in `Individual components` tab

1. Install [Git](https://git-scm.com/download/win) with Bash shell

1. Install [Python 3](https://www.python.org/ftp/python/3.6.1/python-3.6.1.exe)

    - Make sure to check `Add Python 3.6 to PATH`

    - Choose standard install (`Install Now`, requires admin)

    - Verify installation by: `python
   --version` in `cmd` prompt

    - Verify *pip* is also installed: `pip --version` in `cmd` prompt

    - If unable to get python on path, follow [this answer](https://stackoverflow.com/questions/23400030/windows-7-add-path) using location `C:\Users\[user]\AppData\Local\Programs\Python\Python36-32\`

1. Install *meson*

    - In `cmd` prompt **with admin priviledges**: `pip install meson`

1. Install [Boost](https://sourceforge.net/projects/boost/files/boost-binaries/1.64.0/boost_1_64_0-msvc-14.1-32.exe/download)

    - Note: the above link is for VS2017 pre-compiled libraries. To compile from source, you must install at the location: `C:\local\boost_1_64_0`

1. Pull UxAS repositories (from Git Bash shell)

    - `git -c http.sslVerify=false clone https://github.com/afrl-rq/OpenUxAS.git`

    - `git -c http.sslVerify=false clone https://github.com/afrl-rq/LmcpGen.git`

    - `git -c https://github.com/afrl-rq/OpenAMASE.git`

1. Build OpenAMASE

    - Load the OpenAMASE project in NetBeans and click `Build`

1. Auto-create the UxAS messaging library

    - Download released executable from [GitHub](https://github.com/afrl-rq/LmcpGen/releases/download/v1.5.0/LmcpGen.jar)

    - Place `LmcpGen.jar` in `LmcpGen/dist` folder

    - From the Git Bash shell in the root UxAS directory, run `sh RunLmcpGen.sh`

    - Note: For simplicity, make sure the LMCPGen, OpenUxAS, and OpenAMASE repositories follow the folder structure labeled in the [Configure UxAS and Related Projects](#configure-uxas-and-related-projects) section.

1. Prepare build

    - Open VS command prompt (Tools -> Visual Studio Command Prompt)

    - Note: If the Visual Studio Command Prompt is absent from Visual Studio, it is also possible to perform the following actions by searching for the `Developer Command Prompt for VS 2017` application and switching the working directory to the root OpenUxAS directory

    - `python prepare`

    - `meson.py build --backend=vs` This should create a Visual Studio solution in the build folder.

1. Set UxAS as the Startup Project

    - Open the OpenUxAS.sln with Visual Studio, right-click the UxAS project found in the Solution Explorer

    - Select Set as StartUp Project

1. Add the boost library to the Library Directories for the dependent projects

    - With the OpenUxAS solution open in Visaul Studio, right-click the uxas project from the Solution Explorer and select `Properties` from the context menu.

    - Select `VC++ Directories` located within the `Configuration Properties` node in the `uxas Properties Pages` Pop Up

    - In under the general tab, there will be a `Library Directories` option. Add the absolute path of the boost libraries here. Given boost was setup with the instruction above, this path should be `C:\local\boost_1_64_0\lib32-msvc-14.1`

1. Build project with Visual Studio

    - Open project file `OpenUxAS.sln` in the `OpenUxAS/build` directory

    - In the `Solution Explorer`, right-click the `uxas` project, and select `Build` from the context menu

#### Caveats

- The Visual Studio backend for Meson mostly works, but will fail when regenerating build files. If you modify one of the `meson.build` files, delete the `build` directory and run `meson.py build --backend=vs` again. The steps following the `meson.build` command must also be performed.

- The UxAS test suite uses some hardcoded POSIX-style paths, and so does not currently work on Windows.
