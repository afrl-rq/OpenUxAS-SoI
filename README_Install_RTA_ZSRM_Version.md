# Introduction

The Runtime Assurance version of OpenUxAS links with the Zero-Slack Rate Monotonic (zsrmv) scheduler
in order to support temporal enforcement ensuring that even if a bug keeps a task in an infinite
loop, the enforcer will issue periodic safe actions.

To use zsrmv you will need to clone the public zsrmv repository, compile it for your computer, install some
library specification and compile OpenUxAS. To run the demos you will need to install a processor frequency
scaling tool to be able to prevent the processor from switching frequencies on demand.

# Installation Instructions

1. Install the frequency scaling tool.
   To do this you need to install the indicator-cpufreq with the command:
   
      sudo apt-get install indicator-cpufreq

   This will add an applet to the tool bar of your ubuntu desktop.

   You also may need to disable the intel cpu freq api at boot time. To do this make a copy of the
   grub boot configuration file with the command:
   
   	sudo cp /etc/default/grub /etc/default/grub.backup

   Then edit the grub boot configuration file with your favorite editor

   	sudo nano /etc/default/grub

   find the line with "GRUB_CMDLINE_LINUX_DEFAULT" and edit it to add at the end: "intel_pstate=disable" e.g.:

   	GRUB_CMDLINE_LINUX_DEFAULT="quiet splash intel_pstate=disable"

   save the file and regenerate the boot files with:

   	sudo update-grub

   Now try the indicator by selecting of the frequencies shown in the applet. This should fix the frequency.

2. Compile and Install the ZSRMV scheduler

   A. First you need to install the linux kernel headers with the commnad:

      sudo apt-get install linux-headers-$(uname -r)

   B. Then clone the zsrmv scheduler with the command:

      git clone git@github.com:cps-sei/zsrmv.git

   C. Compile the kernel module with command (cd to directory where you clone the repository)

      make

   D. Compile the libraries with

      cd lib/
      make

   E. Fine tune some speed parameters by (inside the lib directory)

      i) fix the cpu frequency to the one you will use for the test. We recommend to use one that is high but not the higher
      (certainly not the "turbo" mode, since it may burn the processor -- or at least turn it off).

      ii) run

      	  gen-speed-params "<description of machine and frequency>"

      iii) recompile the library

      	   make

   F. Modify the library descriptor file and install it

      i) cd .. (parent of lib directory)

      ii) edit zsrmv.pc -- change the prefix assignment to the directory where your zsrmv repository is

      iii) sudo cp zsrmv.pc to /usr/local/lib/pkgconfig/zsrmv.pc


3. Compile OpenUxAS following AFRL SoI instructions (either in netbeans or from the command line). It should now
   be able to link it to the zsrmv library


# Running it

   To run it you first need to install the zsrmv kernel module with the command

     ./load-module.sh

   cd to OpenUxAS/examples/02_Example_WaterwaySearch

   Copy the zsrm parameters in the xml configuration file. This can be done by copying a preconfigured file with:

   	cp cfg_WaterwaySearch-zsrm-100msec.xml cfg_WaterwaySearch.xml

   Run the example by running

       ./runAMASE_WaterwaySearch.sh

       in one window and

       ./runUxAS_WaterwaySearch.sh


       in another one. If the example complains about lack of permissions try using "sudo" when you run the commands.