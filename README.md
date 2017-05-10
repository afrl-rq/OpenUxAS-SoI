# Introduction

UxAS consists of a collection of modular services that interact via a common message passing architecture. Similar in design to Robot Operating System (ROS), each service subscribes to messages in the system and responds to queries. UxAS uses the open-source library ZeroMQ to connect all services to each other. The content of each message conforms to the Light-weight Message Control Protocol (LMCP) format. Software classes providing LMCP message creation, access, and serialization/deserialization are automatically generated from simple XML description documents (see the *LmcpGen* project). These same XML descriptions detail the exact data fields, units, and default values for each message. Since all UxAS services communicate with LMCP formatted messages, a developer can quickly determine the input/output data for each service. In a very real sense, the message traffic in the system exposes the interaction of the services that are required to achieve autonomous behavior.

Consider a simple example: the automated construction of the flight pattern to conduct surveillance of geometric lines (e.g. perimeters, roads, coasts). A “line search task” message describes the line to be imaged and the desired camera angle. Using this input description, a line search service calculates the appropriate waypoints to achieve the proper view angle. When the UAV arrives at the first waypoint corresponding to the line search task, the line search service continuously updates the desired camera pointing location to smoothly step the camera along the intended route.

In addition to surveillance pattern automation, UxAS contains services that automate route planning, coordinate behavior among multiple vehicles, connect with external software, validate mission requests, log and diagram message traffic, and optimize task ordering. In all, UxAS has approximately 30 services.

A core functionality provided by UxAS is the mechanism to calculate near-optimal task allocation across teams of unmanned vehicles. With a collection of tasks that require servicing and a pool of vehicles available to service those tasks, UxAS is able to determine which vehicle should do which task in the proper order. This task assignment pipeline is carried out by a series of services working together in a complex sequence.


# License

*OpenUxAS* is developed by the Air Force Research Laboratory, Aerospace System Directorate, Power and Control Division.
The LMCP specification and all source code for *OpenUxAS* is publicaly released under the Air Force Open Source Agreement
Version 1.0. See LICENSE.md for complete details. The Air Force Open Source Agreement closely follows the NASA Open Source
Agreement Verion 1.3.

# Prerequisites and Dependencies

The primary tools and dependencies to obtain, build, document, and simulate UxAS are:

- Git
- OpenGL
- UUID library
- Boost
- Python 2.7 and Python 3.5
- Meson
- Ninja
- [LmcpGen](https://github.com/afrl-rq/LmcpGen)
- [OpenAMASE](https://github.com/afrl-rq/OpenAMASE) (optional, simulation)
- NetBeans with Java JDK (optional, simulation)
- Doxygen (optional, documentation)
- LaTeX (optional, documentation)

The UxAS build system will download and compile the following external libraries

- Google Test
- ZeroMQ (zeromq, czmq, cppzmq, zyre)
- Sqlite
- Zlib
- Minizip
- Serial

Libraries for XML and GPS message parsing have numerous forks without centralized repository control. Code to build the following libraries is included with UxAS

- PugiXML
- TinyGPS

## Supported Operating Systems

For an Ubuntu 16.04 or Mac OS X system with the listed prerequisite tools installed, UxAS should build from source without issue. Support for Windows is planned, but is not yet available. We recommend an Ubuntu virtual machine for Windows users. 

### Windows: Install Ubuntu in Virtual Machine

1. Download and install [VirtualBox](https://www.virtualbox.org/wiki/Downloads)
2. Download long term [stable Ubuntu release](https://www.ubuntu.com/download/desktop)
3. Add virtual machine: in VirtualBox, select `New`
   - In the `Name` field, type a name (e.g. UbuntuVM)
   - With the `Type` drop-down, select `Linux`
   - Confirm `Version` is `Ubuntu (64-bit)` and click `Next`
   - Use slider to select memory size (at least 2GB is required, recommended 4+ GB), then click `Next`
   - Select `Create a virtual hard disk now` and click `Create`
   - Select `VDI (VirtualBox Disk Image)` and click `Next`
   - Select `Dynamically allocated` and click `Next`
   - Keep the name the same as the virtual machine name
   - Select size (note: this is the max size) of virtual disk using slider
    (required 12GB, recommended 50+ GB) and click `Create`
4. With the virtual machine selected in VirtualBox, click `Start` arrow
   - In the `Select start-up disk` window, click the file folder icon
   - Navigate to the downloaded Ubuntu `.iso` file and click `Open`
   - Click `Install Ubuntu`
   - Select `Download updates while installing Ubuntu` and click `Continue`
   - Confirm that `Erase disk and install Ubuntu` is selected and click `Install Now`
   - Confirm the `Write changes to disk` warning (note this is to the virtual disk) and click `Continue`
   - Select appropriate time zone and click `Continue`
   - Choose appropriate keyboard layout (defaults to English (US)) and click `Continue`
   - Complete the user name form, select `Log in automatically` and click `Continue`
   - After installation, click `Restart Now`
   - On `Please remove the installation medium, then press ENTER` sceen, press `ENTER`
   - Upon reboot, open the search menu (top left icon) and type `updates`
   - Select `Software Updater` and allow all updates
   - Shutdown virtual machine (select gear/power icon on top right)
5. In VirtualBox, select virtual machine then click `Settings` gear icon
   - In the `Display` menu (3rd down, left side), select `Enable 3d Acceleration` and click `OK`
   - In the `General` menu (1st on left), go to `Advanced` tab and choose
    `Bidirectional` in `Shared Clipboard` drop-down menu then click `OK`
6. Re-open virtual machine by clicking the `Start` arrow again
   - In the VirtualBox menu (of the window containing the virtual machine), select Devices->Insert Guest Additions CD Image
   - Click `Run` in the warning box
   - Type password and click `Authenticate`
   - Reboot VM
7. Follow Ubuntu instructions for remainder of configuration

### Installing Prerequisite Tools on Ubuntu Linux

1. Install `git`: in terminal
   - ``` sudo apt-get install git ```
   - ``` sudo apt-get install gitk ```
1. Install OpenGL development headers: in terminal
   - ``` sudo apt-get install libglu1-mesa-dev ```
1. Install unique ID creation library: in terminal
   - ``` sudo apt-get install uuid-dev ```
1. Install Boost libraries (**optional but recommended**; see external dependencies section): in terminal
   - ``` sudo apt-get install libboost-filesystem-dev libboost-regex-dev libboost-system-dev ```
1. Install doxygen and related packages (**optional**): in terminal
   - ``` sudo apt-get install doxygen ```
   - ``` sudo apt-get install graphviz ```
   - ``` sudo apt-get install texlive ```
1. Install pip3: in terminal
   - ``` sudo apt install python3-pip ```
   - ``` sudo -H pip3 install --upgrade pip ```
1. Install pip2: in terminal
   - ``` sudo apt install python-pip ```
1. Install ninja build system: in terminal
   - ``` sudo -H pip3 install ninja ```
1. Install meson build configuration: in terminal
   - ``` sudo -H pip3 install meson ```
1. Install python plotting capabilities (**optional**): in terminal
   - ``` sudo apt install python-tk ```
   - ``` sudo -H pip2 install matplotlib ```
   - ``` sudo -H pip2 install pandas ```
1. Install [NetBeans and Oracle Java JDK](http://www.oracle.com/technetwork/java/javase/downloads/jdk-netbeans-jsp-142931.html) (**optional**)
   - Download the Linux x64 version
   - Run downloaded install script: in terminal
   - ``` cd ~/Downloads; sh jdk-8u131-nb-8_w-linux-x64.sh ```
   - Click `Next` three times, then `Install`
1. Enable C/C++ plug-in in NetBeans (**optional**)
   - Open NetBeans (in Ubuntu search, type ``` NetBeans ```)
   - Choose Tools->Plugins from the top menu
   - In the `Available Plugins` tab, search for `C++`
   - Select `C/C++` and click `Install`
1. Install Oracle Java run-time (required for *LmcpGen*): in terminal
   - ``` sudo add-apt-repository ppa:webupd8team/java ```
   - ``` sudo apt update; sudo apt install oracle-java8-installer ```
   - ``` sudo apt install oracle-java8-set-default ```

### Install Prerequisites on Mac OS X
1. Install [XCode](https://developer.apple.com/xcode/)
1. Enable commandline tools: in terminal ``` xcode-select --install ```
1. Install `homebrew` (must be administrator): in terminal
    ``` sudo ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)" ```
1. Add `homebrew` to path: in terminal ``` echo `export PATH="/usr/local/bin:$PATH"` >> ~/.bash_profile ```
1. Install `git`: in terminal ``` brew install git ```
1. Install unique ID library: in terminal ``` brew install ossp-uuid ```
1. Install Boost library and configure it in a fresh shell: in terminal
   - ``` brew install boost ```
   - ``` echo 'export BOOST_ROOT=/usr/local' >> ~/.bash_profile ```
   - ``` bash ```
1. Install `doxygen` and related packages (**optional**): in terminal
   - ``` brew install doxygen ```
   - ``` brew install graphviz ```
   - ``` brew cask install mactex ```
1. Install pip3: in terminal
   - ``` brew install python3 ```
1. Install pip2: in terminal
   - ``` curl -O https://bootstrap.pypa.io/get-pip.py ```
   - ``` sudo -H python get-pip.py ```
1. Install ninja build system: in terminal
   - ``` brew install cmake ```
   - ``` brew install pkg-config ```
   - ``` sudo -H pip3 install scikit-build ```
   - ``` sudo -H pip3 install ninja ```
1. Install meson build configuration: in terminal
   - ``` sudo -H pip3 install meson ```
1. Install python plotting capabilities (**optional**): in terminal
   - ``` sudo -H pip2 install matplotlib ```
   - ``` sudo -H pip2 install pandas ```
1. Install [Oracle Java run-time](https://java.com/en/download/mac_download.jsp) (required for *LmcpGen*)
1. Install [NetBeans and Oracle Java JDK](http://www.oracle.com/technetwork/java/javase/downloads/jdk-netbeans-jsp-142931.html) (**optional**)
   - Download the Mac OSX version
   - Install .dmg
1. Enable C/C++ plug-in in NetBeans (**optional**)
   - Open NetBeans
   - Choose Tools->Plugins from the top menu
   - In the `Available Plugins` tab, search for `C++`
   - Select `C/C++` and click `Install`


# Configure UxAS and Related Projects

1. Checkout, compile OR download *OpenAMASE* (**optional**)
   - File system layout: *OpenAMASE* should be a sibling to *OpenUxAS*
   - Checkout: `git clone https://github.com/afrl-rq/OpenAMASE.git`
   - Compile: Load provided NetBeans project, click `Build`
   - OR Download: from [GitHub](https://github.com/afrl-rq/OpenAMASE/releases/download/v1.0.0/OpenAMASE.jar), place in `dist` folder
2. Checkout, compile OR download *LmcpGen*
   - File system layout: *LmcpGen* should be a sibling to *OpenUxAS*
   - Checkout: `git clone https://github.com/afrl-rq/LmcpGen.git`
   - Compile: Load provided NetBeans project, click `Build`
   - OR Download: from [GitHub](https://github.com/afrl-rq/LmcpGen/releases/download/v1.0.0/LmcpGen.jar), place in `dist` folder
3. Auto-generate source code for LMCP libraries: in terminal in `OpenUxAS` directory
   - Assuming that in the file system, *LmcpGen* is at the same level as `OpenUxAS`
   - ``` sh RunLmcpGen.sh ```
4. Prepare UxAS specific patches to external libraries: in terminal in `OpenUxAS` directory
   - ``` ./prepare ```

The above preparation (i.e. `./prepare`) needs to be done prior to the first build and any
time a file is modified in one of the `/3rd/wrap_patches` subdirectories or the `/3rd/*.wrap.tmpl` files.

This also needs to be done any time you move or rename your source tree.

# Building at the Command Line
1. Configure for release build: in terminal
   - ``` meson build --buildtype=release ```
2. Configure for debug build: in terminal
   - ``` meson build_debug --buildtype=debug ```
   - These two steps only need to be done prior to the first build. If you
modify the Meson files, just build as normal in step 3 and the changes
will be automatically incorporated.
3. Build UxAS: in terminal
   - ``` ninja -C build all ```
   - This step is the only step necessary in day-to-day development work. It's
the Meson equivalent of `make all`. Note that the name of `ninja` may differ by distro. On Fedora, for example,
it's `ninja-build`.
   - To clean the build, add the `clean` target at the end of your ninja
command: `ninja -C build clean`
4. Run UxAS tests: in terminal
   - ``` ninja -C build test ```
   - Confirm all tests passed
   
## Compiling using NetBeans (Debug Mode)

1. Open NetBeans
2. Select File->New Project
3. Choose `C/C++ Project with Existing Sources` and click `Next`
4. Specify the `OpenUxAS/src` folder
5. Select the `Custom` option under `Select Configuration Mode` and click `Next`
6. No changes under `Pre-Build Action`, click `Next`
7. Set the `Clean Command` to ``` ninja -C build_debug clean ```
8. Set the `Build Command` to ``` ninja -C build_debug ``` and click `Next`
9. No changes under `Source Files`, click `Next`
10. No changes under `Code Assistance Configuration`, click `Next`
11. Change `Project Name` to ``` UxAS ``` and click `Finish`

## Removing External Dependencies

If you ever feel the need to refresh external dependencies, you'll need
to remove both the downloaded files and the expanded directories:

$ ./rm-external

This script depends upon the presence of the patch tarballs installed
in the `/3rd` directory by `./prepare`.

# About External Dependencies

In porting the UxAS build system to Meson/Ninja, we've taken advantage of
`wrap` facility to import and build 3rd-party libraries. The advantage
of this approach is that the main UxAS repo no longer needs to contain
these libraries.

There are some rough edges. The `wrap` facility (as of April 2017) was
designed to store the necessary metadata on a server operated by the
Meson/Ninja maintainers. There's a very short list of wrapped projects
available from this server. Worse, the `wrap` facility is not properly
designed for project-local use: "patches" (often, only the necessary
`meson.build` file) are downloaded by the `wrap` facility, which offers
no provision for relative URLs.

Furthermore, the `patch` file must be in an archive format. This means
that the wrapped project's `meson.build` file must be tarred (actually,
the `wrap` facility will handle other archive formats) for reference
from the project's wrap file, and the wrap file must contain a valid
SHA256 hash of the patch archive file.

Clearly, this will complicate maintenance. On the plus side, once an
external project is properly wrapped, it shouldn't require further work
unless you require a different version of the project.

We've taken the approach of stashing valid `meson.build` files in the
`3rd/wrap_patches` directory. This is the place to store other patched
files (if any) needed for the build of the external project. Note that
"patch" does not refer to a context or unified diff, but rather to an
archive containing new and changed files that overwrite the unzipped
sources. The `wrap` facility is not able to patch using diff files.

## About Boost

Boost is handled slightly differently from the other external
dependencies, in that the build system attempts to use a
system-provided version of Boost before falling back on the `wrap`
facility as a last resort.

Boost uses a bespoke configuration and build system
that is very difficult to replicate with a Meson-based `wrap` build,
and so Meson itself handles Boost differently from other
`pkg-config`-provided system dependencies.

### System-provided Boost

We *strongly* recommend using a system-provided Boost from `brew`,
`apt-get`, etc. If you have a system-provided boost, but during
Meson's configuration phase, you see something like the following, try
setting your `BOOST_ROOT` environment variable to the prefix of your
system-installed packages (most likely `/usr/local` for MacOS with
Homebrew):

```
Dependency Boost (filesystem, regex, system) found: NO
```

If you have a system-provided Boost but this message still does not go
away, [open an issue](https://github.com/afrl-rq/OpenUxAS/issues/new)
with details of your system configuration.

### Boost via Meson wrap

If no system-provided Boost is available, Meson will fall back to
using the `wrap` we maintain alongside the other external
dependencies. This will probably work on 64-bit Linux systems, but
unexpected trouble may arise on other platforms.

# Running the Examples

1. Assuming that in the file system, *OpenAMASE* is at the same level as `OpenUxAS`
2. Add python package for UxAS plotting (src/Utilities/localcoords)
   - ``` sudo -H python setup.py install ```
3. Run examples
   - Example 2: Follow README.md in `examples/02_Example_WaterwaySearch`
   - Example 3: Follow README.md in `examples/03_Example_DistributedCooperation`
   
# Building the Documentation

1. The User Manual can be generated by running:
   `pdflatex UxAS_UserManual.tex` in the folder `doc/doxygen/reference/UserManual/`
2. Create HTML Doxygen reference documenation:
   - Open terminal in directory `doc/doxygen`
   - ``` sh RunDoxygen.sh ```
   - In newly created `html` folder, open index.html
3. Doxygen PDF reference manual can be created by:
   - Copy the line from `ExtraLineToFixLatex.txt` into `doc/doxygen/latex/refman.tex` just above the line `%===== C O N T E N T S =====`
   - In the folder `doc/doxygen/latex` run the command `pdflatex refman.tex`
   - The complete reference manual can be found at `doc/doxygen/latex/refman.pdf`
