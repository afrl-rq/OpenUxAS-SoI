File structure description with explanations of functionality of each part
==========================================================================

This section outlines the file structure of UxAS with descriptions and explanations of each part.
Figure [Open UxAS Folder] shows the UxAS folder and the folders housing its dependent projects. It is recommended that the OpenAMASE, LmcpGen, and OpenUxAS projects are placed in the same directory. The OpenAMASE project is used to run simulations with simulated aircraft. The LmcpGen project is used to generate LMCP messages.  

![Open UxAS Folder](UxasAndDependentProjects.png =250x )

Within OpenUxAS there is a series of folders. These folders include 3rd, doc, examples, mdms, resources, src, and tests. These folders can be seen in figure \ref{OpenUxASFolderContents}. The 3rd folder contains UxAS's dependent libraries. The doc folder contains UxAS documentation. The examples folder holds a series of configurations that are necessary to execute a simulation with OpenUxAS and OpenAMASE. The MDMs folder contains Message Data Modules that are used by LMCP to define custom sets of messages for each target system. The resources folder contains a series of scripts that can be used to analyze a simulation. The src folder contains the source code for OpenUxAS. The tests folder contains the unit tests.

![Open UxAS Folder Contents \label{OpenUxASFolderContents}](/Figures/OpenUxASFolder.png =250x)

The contents of the doc folder can be seen in figure \ref{DocFolder}. This folder contains additional folders named doxygen, LMCP, and reference. The doxygen folder holds the files required to run doxygen and perform code inspection with the doxygen output. The LMCP folder contains files that describe the Message Data Modules. The reference folder contains UxAS flow charts, sequence diagrams, and the UxAS user manual.

![Documents Folder Contents \label{DocFolder}](/Navigating/Figures/DocFolder.png =250x)

The examples folder contains folders that contain configuration files required to execute a UxAS simulation. This folder can be seen in figure \ref{ExamplesFolder}. Most of the simulations cannot be executed without OpenAMASE.

![Examples Folder Contents \label{ExamplesFolder}](/Navigating/Figures/ExamplesFolder.png =250x)

The mdms folder contains the message data modules. This folder can be seen in figure \ref{MdmsFolder}. These configuration files are used by LMCP to define custom sets of messages for each target system.

![MDMs Folder \label{MdmsFolder}](/Navigating/Figures/MdmsFolder.png =250x)

The resources folder contains a series of scripts that can be used to analyze a simulation. The resources folder can be seen in figure \ref{ResourcesFolder}.

![Recources Folder \label{ResourcesFolder}](/Navigating/Figures/ResourcesFolder.png =250x)

The src folder contains the OpenUxAS source code. The src folder contains the OpenUxAS source code. This includes all of the header and implementation files. The contents of this folder can be seen in figure \ref{SrcFolder}.

![Source Folder \label{SrcFolder}](/Navigating/Figures/SrcFolder.png =250x)

The test folder contains all the unit tests that can be run to assess the messages that UxAS sends. This folder can be seen in figure \ref{TestsFolder}.

![Tests Folder \label{TestsFolder}](/Navigating/Figures/TestFolder.png =250x)


Architecture and messaging
==========================
