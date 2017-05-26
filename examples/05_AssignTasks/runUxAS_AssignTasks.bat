mkdir RUNDIR_AssignTasks
cd RUNDIR_AssignTasks
rmdir /S /Q datawork
rmdir /S /Q log
..\..\..\build\uxas.exe -cfgPath ..\cfg_AssignTasks.xml
