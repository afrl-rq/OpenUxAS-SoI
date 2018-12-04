# ** UxAS/ Docker Quickstart **
* Updated - `7/19/2018`

# DICLAIMER: This is a work in progress. 

# Visual Studio Code Debugging
* `7/16/2018` - Debugging with VS Code
* The directory `OpenUxAS/docker/VSCodeFiles/` contains configuration
  files that setup VS Code for debugging UxAS inside the Docker container
* The approach is to run the `uxas-build` Docker container interactively.
  Then use VS Code to start with `gdb` in the container and control it with the
  VS code debugging tools
* In VS Code the steps are:
    * run the task: `03_buildDebug (Docker)` to bulid a debug version of the 
      UxAS code.
    * run the task: `05_StartDockerDebugContainer` this runs a docker container named `uxas_debug`, based on the `uxas-build`
    docker image, in interactive mode.
    * click on the `Debug` icon on the left side of the VS Code window.
    * Start the debugger by clicking on the `green` debug launch button
* NOTE: once the `uxas_debug` Docker container is started, it will keep
        running until stopped. UxAS can be built and debugged
        without stopping the `uxs_debug` container.


## Manual `gdb` Debugging
* `7/16/2018` - manual gdb debugging
* * starting UxAS using gdbserver in uxas-build container
* * MACOS: (cross) compliled gbd with flag to make it possible to connect to the (LINUX) container

### APPROACH
Using `gdb` / `gdbserver` to remotely connect a debugger from the `host` operating system (OS)
to a copy of UxAS running in a Docker container. NOTE: If the `host` OS is different from that of
the container (LINUX), then `gdb` must be compile with the proper flags to interpret the UXAS
executable running in the container.

### DEBUGGING
1) Build a debug version of UxAS :
   `python 07_Build_UxAS_Debug.py`
2) Start `gdbserver` in a `uxas-build` container, adding UxAS arguments:
   There is an example of starting the gdbserver, in a `uxas-build` container, in the directory `09_test_debug`
3) Start `gdb`, point at the `host` copy of the UxAS executable compile for the
   container:
   `/opt/gdb/x86_64-linux-gnu/cross/bin/x86_64-linux-gnu-gdb ../tmp/debug/uxas`
4) In `gdb` set the taegert to the container's remote port:
   (gdb) `target remote :8298`
   
### BUILDING GDB
If the `host` OS is different from that of the container, then download and build a `cross` version of gdb for
the host, see [https://www.linux.com/news/remote-cross-target-debugging-gdb-and-gdbserver]
