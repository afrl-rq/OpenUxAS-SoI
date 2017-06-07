# License

*OpenUxAS* is developed by the Air Force Research Laboratory, Aerospace System Directorate, Power and Control Division. 
The LMCP specification and all source code for *OpenUxAS* is publicaly released under the Air Force Open Source Agreement
Version 1.0. See LICENSE.md for complete details. The Air Force Open Source Agreement closely follows the NASA Open Source
Agreement Verion 1.3. **NOTE the terms of the license include registering use of the software by emailing <a href="mailto:afrl.rq.opensource@us.af.mil?subject=OpenUxAS Registration&body=Please register me for use of OpenUxAS. Name: ____________">afrl.rq.opensource@us.af.mil</a>.**

# Introduction

UxAS consists of a collection of modular services that interact via a common message passing architecture. Similar in design to Robot Operating System (ROS), each service subscribes to messages in the system and responds to queries. UxAS uses the open-source library ZeroMQ to connect all services to each other. The content of each message conforms to the Light-weight Message Control Protocol (LMCP) format. Software classes providing LMCP message creation, access, and serialization/deserialization are automatically generated from simple XML description documents (see the *LmcpGen* project). These same XML descriptions detail the exact data fields, units, and default values for each message. Since all UxAS services communicate with LMCP formatted messages, a developer can quickly determine the input/output data for each service. In a very real sense, the message traffic in the system exposes the interaction of the services that are required to achieve autonomous behavior.

Consider a simple example: the automated construction of the flight pattern to conduct surveillance of geometric lines (e.g. perimeters, roads, coasts). A “line search task” message describes the line to be imaged and the desired camera angle. Using this input description, a line search service calculates the appropriate waypoints to achieve the proper view angle. When the UAV arrives at the first waypoint corresponding to the line search task, the line search service continuously updates the desired camera pointing location to smoothly step the camera along the intended route.

In addition to surveillance pattern automation, UxAS contains services that automate route planning, coordinate behavior among multiple vehicles, connect with external software, validate mission requests, log and diagram message traffic, and optimize task ordering. In all, UxAS has approximately 30 services.

A core functionality provided by UxAS is the mechanism to calculate near-optimal task allocation across teams of unmanned vehicles. With a collection of tasks that require servicing and a pool of vehicles available to service those tasks, UxAS is able to determine which vehicle should do which task in the proper order. This task assignment pipeline is carried out by a series of services working together in a complex sequence.

# Quick Start (only if you already have Ubuntu 16.04 LTS installed!!):

Try:

    mkdir -p /home/$USER/UxAS_pulls
    cd /home/$USER/UxAS_pulls
    git clone https://github.com/afrl-rq/OpenUxAS.git
    cd OpenUxAS
    git checkout BRANCH
    ./install_most_deps.sh
    ./checkout_plus_config.sh -d /home/$USER/UxAS_pulls BRANCH
    ./build_documentation

replacing ***BRANCH*** with the branch of OpenUxAS that you want (e.g., develop, architecture, rta ...). (It's recommended that you use `/home/$USER/UxAS_arch` for the directory if you're using the `archtiecture` branch, rather than `/home/$USER/UxAS_pulls` for the `develop` branch.)

Make sure you follow the instructions in the terminal window, and press a key once you're ready to move to the next set of instructions.

(Note that if you see a '$' prompt during install_most_deps.sh, that you'll need to type 'Ctrl-C' and 'Ctrl-D' once each to continue running the script.)

To test OpenUxAS 'example 2', try:
1. In terminal 1:

    `cd /home/$USER/UxAS_pulls/OpenUxAS/examples/02_Example_WaterwaySearch`  
    `./runAMASE_WaterwaySearch.sh`

1. Press the 'play' button in the AMASE simulation player.
1. In terminal 2:

    `cd /home/$USER/UxAS_pulls/OpenUxAS/examples/02_Example_WaterwaySearch`  
    `./runUxAS_WaterwaySearch.sh`

If you need to recompile OpenUxAS later, try:

    cd ~/UxAS_pulls/OpenUxAS
    ninja -C build all

If you need to pull the newest versions of the UxAS code from the server and recompile, try:

    cd /home/$USER/UxAS_pulls/OpenUxAS
    ./checkout_plus_config.sh -d /home/$USER/UxAS_pulls BRANCH
    
replacing ***BRANCH*** with the branch of OpenUxAS that you want (e.g., develop, architecture, rta ...).

Alternately, if you change your mind after the fact and want to use (e.g.) the architecture branch for things, try:

    cd /home/$USER/UxAS_pulls/OpenUxAS
    ./checkout_plus_config.sh -d /home/$USER/UxAS_pulls architecture


# Prerequisites and Dependencies

The primary tools and dependencies to obtain, build, document, and simulate UxAS are:

- Git
- OpenGL
- UUID library
- Boost
- Python 3
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

For an Ubuntu 16.04 or Mac OS X system with the listed prerequisite tools installed, UxAS should build from source without issue. Native Windows support is currently experimental—we recommend using an Ubuntu virtual machine for a smoother experience. 

Support for Windows is available on Windows 10, with some caveats.

### For Windows 10 users only: Install "Bash on Ubuntu on Windows", Windows Subsystem for Linux (Optional)

If you are a Windows 10 user and don't want to use VirtualBox (or otherwise don't have very many cores to play with), you also have the alternate option of installing a local Ubuntu 16.04 bash instance and trying to compile UxAS within that environment.

To set this up:
1. Update to the Windows 10 Creators Update
1. [Install Bash on Ubuntu on Windows](https://msdn.microsoft.com/en-us/commandline/wsl/install_guide) for a Ubuntu 16.04 shell
1. [Install XMing](https://sourceforge.net/projects/xming/) for an XWindows interface that allows GUI windows to be seen. At the bash command prompt, you'll also want to run each of these commands once:
   - `echo "export DISPLAY=:0" >> ~/.bashrc`
   - `sudo apt update & sudo apt install gedit`

This has been tested-working for the UxAS project, but may not work for other packages or programs (such as ROS). :)

### Windows: Install Ubuntu in Virtual Machine

1. Download and install [VirtualBox](https://www.virtualbox.org/wiki/Downloads)
1. Download long term [stable Ubuntu release](https://www.ubuntu.com/download/desktop)
1. Add virtual machine: in VirtualBox, select `New`
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
1. With the virtual machine selected in VirtualBox, click `Start` arrow
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
1. In VirtualBox, select virtual machine then click `Settings` gear icon
   - In the `Display` menu (3rd down, left side), select `Enable 3d Acceleration` and click `OK`
   - In the `General` menu (1st on left), go to `Advanced` tab and choose
    `Bidirectional` in `Shared Clipboard` drop-down menu then click `OK`
1. Re-open virtual machine by clicking the `Start` arrow again
   - In the VirtualBox menu (of the window containing the virtual machine), select Devices->Insert Guest Additions CD Image
   - Click `Run` in the warning box
   - Type password and click `Authenticate`
   - Reboot VM
1. Follow Ubuntu instructions for remainder of configuration

### Installing Prerequisite Tools on Ubuntu Linux / Bash on Ubuntu on Windows -or- Mac OS X (Partially-Automated)

The following is a bash script that helps to partially-automate the "installing prerequisite tools" processes that are documented in this README.md file below.

This has been tested-working on Ubuntu 16.04, as of 2016-05-23.

1. Download the script from the [*OpenUxAS* repository](https://github.com/afrl-rq/OpenUxAS/) (install_most_deps.sh) OR `cd` to your `git clone`d *OpenUxAS* directory
1. Run the script at the terminal: `./install_most_deps.sh`
1. Follow the on-screen instructions

Note that the most up-to-date instructions on the dependencies-needed for UxAS are available below.

### Installing Prerequisite Tools on Ubuntu Linux

1. Install `git`: in terminal
   - `sudo apt-get install git`
   - `sudo apt-get install gitk`
1. Install OpenGL development headers: in terminal
   - `sudo apt-get install libglu1-mesa-dev`
1. Install unique ID creation library: in terminal
   - `sudo apt-get install uuid-dev`
1. Install Boost libraries (**optional but recommended**; see external dependencies section): in terminal
   - `sudo apt-get install libboost-filesystem-dev libboost-regex-dev libboost-system-dev`
1. Install doxygen and related packages (**optional**): in terminal
   - `sudo apt-get install doxygen`
   - `sudo apt-get install graphviz`
   - `sudo apt-get install texlive`
   - `sudo apt-get install texlive-latex-extra`
1. Install pip3: in terminal
   - `sudo apt install python3-pip`
   - `sudo -H pip3 install --upgrade pip`
1. Install ninja build system: in terminal
   - `sudo -H pip3 install ninja`
1. Install meson build configuration: in terminal
   - `sudo -H pip3 install meson`
1. Ensure dependency search for meson is supported: in terminal
   - `sudo apt-get install pkg-config`
1. Install python plotting capabilities (**optional**): in terminal
   - `sudo apt install python3-tk`
   - `sudo -H pip3 install matplotlib`
   - `sudo -H pip3 install pandas`
1. Install [NetBeans and Oracle Java JDK](http://www.oracle.com/technetwork/java/javase/downloads/jdk-netbeans-jsp-142931.html) (**optional**)
   - Download the Linux x64 version
   - Run downloaded install script: in terminal
   - `cd ~/Downloads; sh jdk-8u131-nb-8_w-linux-x64.sh`
   - Click `Next` three times, then `Install`
1. Enable C/C++ plug-in in NetBeans (**optional**)
   - Open NetBeans (in Ubuntu search, type `NetBeans`)
   - Choose Tools->Plugins from the top menu
   - In the `Available Plugins` tab, search for `C++`
   - Select `C/C++` and click `Install`
1. Install Oracle Java run-time (required for *LmcpGen*): in terminal
   - `sudo add-apt-repository ppa:webupd8team/java`
   - `sudo apt update; sudo apt install oracle-java8-installer`
   - `sudo apt install oracle-java8-set-default`

### Install Prerequisites on Mac OS X
1. Install [XCode](https://developer.apple.com/xcode/)
1. Enable commandline tools: in terminal `xcode-select --install`
1. Install `homebrew` (must be administrator): in terminal
    `sudo ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"`
1. Add `homebrew` to path: in terminal `echo $(export PATH="/usr/local/bin:$PATH") >> ~/.bash_profile`
1. Install `git`: in terminal `brew install git`
1. Install unique ID library: in terminal `brew install ossp-uuid`
1. Install Boost library and configure it in a fresh shell: in terminal
   - `brew install boost`
   - `echo 'export BOOST_ROOT=/usr/local' >> ~/.bash_profile`
   - `bash`
1. Install `doxygen` and related packages (**optional**): in terminal
   - `brew install doxygen`
   - `brew install graphviz`
   - `brew cask install mactex`
1. Install pip3: in terminal
   - `brew install python3`
1. Install ninja build system: in terminal
   - `brew install cmake`
   - `brew install pkg-config`
   - `sudo -H pip3 install scikit-build`
   - `sudo -H pip3 install ninja`
1. Install meson build configuration: in terminal
   - `sudo -H pip3 install meson`
1. Install python plotting capabilities (**optional**): in terminal
   - `sudo -H pip3 install matplotlib`
   - `sudo -H pip3 install pandas`
1. Install [Oracle Java run-time](https://java.com/en/download/mac_download.jsp) (required for *LmcpGen*)
1. Install [NetBeans and Oracle Java JDK](http://www.oracle.com/technetwork/java/javase/downloads/jdk-netbeans-jsp-142931.html) (**optional**)
   - Download the Mac OSX version
   - Install .dmg
1. Enable C/C++ plug-in in NetBeans (**optional**)
   - Open NetBeans
   - Choose Tools->Plugins from the top menu
   - In the `Available Plugins` tab, search for `C++`
   - Select `C/C++` and click `Install`

### Prep and Build on Native Windows

The native Windows build is currently experimental. See below for caveats, and contact @acfoltzer if you encounter problems.

1. Install [Visual Studio 2017](https://www.visualstudio.com/downloads/) with the C++ workflow and support for Git and GitHub.
1. Install the latest version of [Python 3.x](https://www.python.org/downloads/). In the installer, make sure to check the option to configure environment variables.
1. Open a command prompt with administrator privileges, and install Meson: `pip install meson`.
1. Download and install the [Boost libraries](https://sourceforge.net/projects/boost/files/boost-binaries/1.64.0/boost_1_64_0-msvc-14.1-32.exe/download).
1. Use the Visual Studio Team Explorer to check out OpenUxAS; this is easiest by entering your GitHub credentials.
1. Open the OpenUxAS folder in the Solution Explorer, right click it, and open a developer command prompt.
1. In the command prompt, type:
   ```
   python prepare
   meson.py build --backend=vs
   ```
1. Back in the Solution Explorer, you should now see a `build` directory containing a UxAS solution. Open that solution.
1. In the Solution Explorer, right-click the `uxas` project, and click Build.
1. To test your build, try running the `.bat` scripts in the `examples` directories (you will need to build OpenAMASE using NetBeans and a JDK for some of the examples).

#### Caveats

- The Visual Studio backend for Meson mostly works, but will fail when regenerating build files. If you modify one of the `meson.build` files, delete the `build` directory and run `meson.py build --backend=vs` again.
- The Ninja backend for Meson currently does not pull in the correct static Boost libraries. We have submitted a patch upstream to fix this, but it has not yet landed in a Meson release.
- The UxAS test suite uses some hardcoded POSIX-style paths, and so does not currently work on Windows.

# Configure and Build UxAS and Related Projects

## Configure UxAS and Related Projects + Building at the Command Line on Ubuntu Linux / Bash on Ubuntu on Windows -or- Mac OS X (Partially-Automated)

The following is a bash script that helps to partially-automate the "configure UxAS and related projects" and "building at the command line" processes that are documented in this README.md file below.

This has been tested-working on Ubuntu 16.04, as of 2016-05-23.

1. Download these two scripts from the [*OpenUxAS* repository](https://github.com/afrl-rq/OpenUxAS/) OR `cd` to your `git clone`d *OpenUxAS* directory
    - `checkout_plus_config.sh`
    - `get_dlvsco_wd_f.sh`
1. Run the `checkout_plus_config.sh` script at the terminal:
    - If you want to download the .jar files for OpenAMASE and LmcpGen, try: `./checkout_plus_config.sh -d`
    - If you want to compile the .jar files for OpenAMASE and LmcpGen, try: `./checkout_plus_config.sh -c`
1. Follow the on-screen instructions

Note that this sets up your UxAS workspace under a default directory (`/home/$USER/UxAS_pulls`). If you want to specify a workspace other than the default, then pass the absolute path to the script as a second argument when calling the script (e.g., `./checkout_plus_config.sh -d /home/$USER/my_checkout_dir`).


## Configure UxAS and Related Projects

Expected file system layout:
```
./
  OpenAMASE
          /OpenAMASE
                    /config
                    /data
                    /dist
                         OpenAMASE.jar <-- add this here to avoid compilation
                    /docs
                    /example scenarios
                    /lib
                    /native
                    /nbproject
                    /run
                    /src
  LcmpGen
          /dist
               LmcpGen.jar <-- add this here to avoid compilation
          /nbproject
          /src
  OpenUxAS
          /3rd
          /doc
          /examples
          /mdms
          /resources
          /src
          /tests
          /wrap_patches
```

1. EITHER Checkout + compile *OpenAMASE* (**optional**)
   - File system layout: *OpenAMASE* should be a sibling to *OpenUxAS* (see above)
   1. Checkout: `git clone https://github.com/afrl-rq/OpenAMASE.git`
   2. Compile: Load provided Netbeans project, click `Build`  
   
   OR Download *OpenAMASE* (**optional**)
   - File system layout: *OpenAMASE* should be a sibling to *OpenUxAS* (see above)
   1. Download: from [GitHub](https://github.com/afrl-rq/OpenAMASE/releases/download/v1.0.0/OpenAMASE.jar)
   2. Place `OpenAMASE.jar` in `OpenAMASE/OpenAMASE/dist` folder
2. EITHER Checkout + compile *LmcpGen*
   - File system layout: *LmcpGen* should be a sibling to *OpenUxAS* (see above)
   1. Checkout: `git clone https://github.com/afrl-rq/LmcpGen.git`
   2. Compile: Load provided Netbeans project, click `Build`  
   
   OR Download *LmcpGen*
   - File system layout: *LmcpGen* should be a sibling to *OpenUxAS* (see above)
   1. Download: from [GitHub](https://github.com/afrl-rq/LmcpGen/releases/download/v1.1.0/LmcpGen.jar)
   2. Place `LmcpGen.jar` in `LmcpGen/dist` folder
3. Auto-generate source code for LMCP libraries: in terminal in `OpenUxAS` directory
   - Assuming that in the file system, *LmcpGen* is at the same level as `OpenUxAS` (see above)
   - `sh RunLmcpGen.sh`
4. Prepare UxAS specific patches to external libraries: in terminal in `OpenUxAS` directory
   - `./prepare`

The above preparation (i.e. `./prepare`) needs to be done prior to the first build and any
time a file is modified in one of the `/3rd/wrap_patches` subdirectories or the `/3rd/*.wrap.tmpl` files.

This also needs to be done any time you move or rename your source tree.

## Building at the Command Line
1. Configure for release build: in terminal
   - `meson build --buildtype=release`
1. Configure for debug build: in terminal
   - `meson build_debug --buildtype=debug`
   - These two steps only need to be done prior to the first build. If you
modify the Meson files, just build as normal in step 3 and the changes
will be automatically incorporated.
1. Build UxAS: in terminal
   - `ninja -C build all`
   - This step is the only step necessary in day-to-day development work. It's
the Meson equivalent of `make all`. Note that the name of `ninja` may differ by distro. On Fedora, for example,
it's `ninja-build`.
   - To clean the build, add the `clean` target at the end of your ninja
command: `ninja -C build clean`
1. Run UxAS tests: in terminal
   - `ninja -C build test`
   - Confirm all tests passed
   
### Compiling using NetBeans (Debug Mode)

1. Open NetBeans
1. Select File->New Project
1. Choose `C/C++ Project with Existing Sources` and click `Next`
1. Specify the `OpenUxAS` folder
1. Select the `Custom` option under `Select Configuration Mode` and click `Next`
1. No changes under `Pre-Build Action`, click `Next`
1. Set the `Clean Command` to `ninja -C build_debug clean`
1. Set the `Build Command` to `ninja -C build_debug uxas` and click `Next`
1. No changes under `Source Files`, click `Next`
1. No changes under `Code Assistance Configuration`, click `Next`
1. Change `Project Name` to `UxAS` and click `Finish`

For Linux systems, Netbeans will automatically use the `gdb` debugger. On Mac OS X,
`gdb` must be installed and signed (see [Neil Traft's guide](http://ntraft.com/installing-gdb-on-os-x-mavericks/)).

### Removing External Dependencies

If you ever feel the need to refresh external dependencies, you'll need
to remove both the downloaded files and the expanded directories:

`./rm-external`

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
1. Add python package for UxAS plotting (src/Utilities/localcoords)
   - `sudo -H python3 setup.py install`
1. Run examples
   - Example 2: Follow README.md in `examples/02_Example_WaterwaySearch`
   - Example 3: Follow README.md in `examples/03_Example_DistributedCooperation`
   
# Building the Documentation

## Building the Documentation on Ubuntu Linux / Bash on Ubuntu on Windows -or- Mac OS X (Partially-Automated)

The following is a bash script that helps to partially-automate the "building the documentation" processes that are documented in this README.md file below.

This has been tested-working on Ubuntu 16.04, as of 2016-05-23.

1. Download the script from the [*OpenUxAS* repository](https://github.com/afrl-rq/OpenUxAS/) (build_documentation.sh) OR `cd` to your `git clone`d *OpenUxAS* directory
1. Run the script at the terminal: `./build_documentation.sh`
1. Follow the on-screen instructions

Note that this will pop open two html files in your webbrowser and also the pdf manual when run.

## Building the Documentation Manually

If you'd like to do this process manually, then:

1. The User Manual can be generated by running:
   `pdflatex UxAS_UserManual.tex` in the folder `doc/reference/UserManual/`
1. Create HTML Doxygen reference documenation:
   - Open terminal in directory `doc/doxygen`
   - `sh RunDoxygen.sh`
   - In newly created `html` folder, open index.html
1. Doxygen PDF reference manual can be created by:
   - Copy the line from `ExtraLineToFixLatex.txt` into `doc/doxygen/latex/refman.tex` just above the line `%===== C O N T E N T S =====`
   - In the folder `doc/doxygen/latex` run the command `pdflatex refman.tex`
   - The complete reference manual can be found at `doc/doxygen/latex/refman.pdf`

# Branching and Repository Management

The OpenUxAS branching model addresses the following concerns:

- We have a stable branch that always builds and passes tests
- Multiple collaborative teams can proceed with their development
  independently
- Discrete features can be contributed to the main line of OpenUxAS
  development, and these can be integrated into other teams' ongoing
  work
- Until OpenUxAS is public, all teams can use the `afrl-rq`
  organization's Travis-CI account for continuous integration

To address these concerns, OpenUxAS uses a variant on
the [Git Flow][git-flow], [GitLab Flow][gitlab-flow],
and [GitHub flow][github-flow] models.

[git-flow]: http://nvie.com/posts/a-successful-git-branching-model/
[gitlab-flow]: https://docs.gitlab.com/ee/workflow/gitlab_flow.html
[github-flow]: https://guides.github.com/introduction/flow/

Because OpenUxAS does not yet have a fixed cycle of releases, we do
not need the additional complexity of `hotfix/` and `release/`
branches present in Git Flow. However, since a number of collaborating
teams work on OpenUxAS simultaneously, it makes sense to have
long-lived branches for each team, rather than only having feature
branches and a stable branch.

This README does not go into detail about the various Flow models, but
instead provides instructions for common scenarios. We encourage you
to read about the Flow models to get more of a sense for the "why";
here we are focusing on the "how".

## Quick Overview

The repository will typically have a branching structure like the following:

- `master`
  - very stable, only updated by pull request from `develop`
- `develop`
  - stable, only updated by pull request from feature branches
- `teamA`
  - team branch for Team A
  - stable at the discretion of Team A
  - updated by merging in feature branches and `develop`
- `teamA-feature1`
  - feature branch for Team A
  - when finished, merged into `develop` via pull request
- `teamB`
- `teamB-feature1`
- etc.

## Team Branches

The team branch is the branch off of which your team will work. It
serves the role of the `develop` branch of Git Flow or the `master`
branch of GitLab and GitHub Flow. This branch is never intended to be
directly merged back into `develop`, but feature branches based off of
it will be.

If you have experience with these models, this concept probably seems
odd. Eventually, we would like to replace these team branches with
entire repo forks for each team, but until OpenUxAS is public, this
would prevent forks from using the `afrl-rq` Travis-CI account.

### Creating

Start by creating a new branch that will serve as the active
development branch for your team. This step should only be necessary
once for your team; this branch is meant to be long-lived as opposed to a
feature branch that is quickly merged in and deleted.

```shell
$ git checkout develop
$ git checkout -b teamA
```

### Updating

You will want to regularly incorporate the latest changes from the
`develop` branch in your team branch. This reduces the pain when
merging your team's changes back into `develop`.

Start by making sure your local `develop` branch is up-to-date:

```shell
$ git checkout develop
$ git pull
```

Then merge the updated `develop` with your team branch:

```shell
$ git checkout teamA
$ git merge develop
```

## Feature Branches

Feature branches are shorter-lived branches meant to encompass a
particular effort or feature addition. These branches will be the
means for you to incorporate your team's changes into the main
`develop` branch via pull requests.

Feature branches will always be based off of your team branch, so if
your team branch has commits you would like to see in `develop`, you
can simply create a new feature branch and begin the pull request
process right away.

### Naming

To help the OpenUxAS maintainers know which branches belong to which
teams, feature branches should be named using your team name as a
prefix, for example `teamA-feature1`.

### Creating

Create a feature branch by checking it out off of your team
branch. Note that it will save you some effort at the later merge to
update your team branch from `develop` first.

```shell
$ git checkout teamA
$ get checkout -b teamA/feature1
```

### Merging to Team Branch

For a long-running feature branch, you may want to occasionally merge
it back into your team branch so it can be shared within your team
before it's ready to be merged into `develop`.

```shell
$ git checkout teamA
$ git merge teamA/feature1
```

### Merging to `develop`

You cannot directly merge a feature branch into `develop`, because it
is protected. Instead, open a pull request from the feature branch
into `develop`, and your changes will be merged after review.

It is a good idea to update your team branch and delete your feature
branch once it is merged into `develop`.

```shell
$ git checkout develop
$ git pull
$ git checkout teamA
$ git merge develop
$ git push origin --delete teamA/feature1
$ git branch -d teamA/feature1
```
