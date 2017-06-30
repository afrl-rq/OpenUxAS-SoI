mkdir RUNDIR_WaterwaySearch
cd RUNDIR_WaterwaySearch
rmdir /S /Q datawork
rmdir /S /Q log
..\..\..\build\uxas.exe -cfgPath ..\cfg_WaterwaySearch.xml

