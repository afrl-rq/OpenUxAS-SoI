# Visual Studio Code Files 
* Updated - `7/23/2018`

The files in the directory can be used to configure 
VS Code to build, clean, and debug UxAS inside docker
containers.

## VS Code
* VS Code website: [https://code.visualstudio.com]
* To use the `.json` configuration files, copy then to the directory:
`OpenUxAS/.vscode` and then open VS Code.
* After installing VS Code install the `C/C++` VS Code extension 
* There are also very good VS Code extensions such as those for Docker, git, markdown, python, and many others.


## Configuration Files
* `launch.json` - starts `gdb` in the (running) `uxas_debug`
  container
* `settings.json` - sets up `files.exclude` to only show source
  code files
* `tasks.json` - defines the build, clean, debug tasks


## Tasks
   Choose `Tasks->Run Task` from the VS Code menu and then select
   the task in the resulting drop-down
### Build Release Version of UxAS
    * run the task: `01_buildRelease (Docker)` this runs the code:
    `03_BuildDeploy_UxAS.py` which builds a release version
    of UxAS and creates the `uxas-deploy` image
### Clean Release Build Files
    * run the task: `02_CleanReleaseBuild` this runs the code:
    `06_RemoveBuildFiles.py` which removes the `build` files
    from the docker volume, `UxAS_Build_Vol`
### Build Debug Version of UxAS
    * run the task: `03_buildDebug (Docker)` this runs the code:
    `08_Build_UxAS_Debug.py` which builds a debug version of UxAS 
    which is stored in the docker volume, `UxAS_Build_Vol`.
### Clean Debug Build Files
    * run the task: `04_CleanDebugBuild` this runs the code:
    `09_RemoveDebugBuildFiles.py` which removes the `build_debug` files
    from the docker volume, `UxAS_Build_Vol`
### Debug UxAS
    * run the task: `05_StartDockerDebugContainer` this runs the `uxas-build` docker container in interactive mode.
    * click on the `Debug` icon on the left side of the VS Code window.
    * Start the debugger by clicking on the `green` debug launch button
### Remove the UxAS Source from the Docker Volume
    * run the task: `06_RemoveDockerSource` this runs the code:
    `09_RemoveDebugBuildFiles.py` which removes the `source` files
    from the docker volume, `UxAS_Build_Vol`


