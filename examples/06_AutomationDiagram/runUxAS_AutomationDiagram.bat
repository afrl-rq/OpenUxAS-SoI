mkdir RUNDIR_AutomationDiagram
cd RUNDIR_AutomationDiagram
rmdir /S /Q datawork
rmdir /S /Q log
..\..\..\build\uxas.exe -cfgPath ..\AutomationDiagram_cfg.xml
