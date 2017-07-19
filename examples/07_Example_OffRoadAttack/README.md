# Waterway Search Off Road Attack Example

This is an example of running UxAS service that communicates to the Amase simulation in order to generate plans and an assignment for one of two UAVs to monitor a waterway. For more background see the file 'doc/UxAS_UserManual.pdf'

For OffRoad Attack, an attack will be launched at 40s, which can modify the path of the UAV, redirect the UAV to another position which is not planned. the launch time could be configured by the argument "TimeBetweenMissionCommandsMin_ms" in cfg_WaterwaySearch_OffRoadAttack.xml, also, the redirected coordinate could be configured by "AttackFirstLat" and "AttackFirstLon" in the same file.

For BackToBegin Attack, an attack will be launched at 40s, which can modify the path of the UAV, redirect the UAV to starting positon. the launch time could be configured by the argument "TimeBetweenMissionCommandsMin_ms" in cfg_WaterwaySearch_OffRoadAttack.xml.

## Files:

* `cfg_WaterwaySearch_OffRoadAttack.xml` - This is config file for excuting waterway search task and "OffRoad" attack
* `runUxAS_WaterwaySearch_OffRoadAttack.sh` - command to run UxAS waterway search task along with the malicious OffRoad service.
* 'cfg_WaterwaySearch_BackToBeginAttack.xml' - This is config file for excuting waterway search task and "BackToBegin" attack 
* 'runUxAS_WaterwaySearch_OffRoadAttack.sh' - command to run UxAS waterway search task along with the malicious BackToBegin service.
* `runAMASE_WaterwaySearch.sh` - 
* `Scenario_WaterwaySearch.xml` -
* `MessagesToSend/` - most of the messages in this directory are explained in the document, `WaterwayExample_MessageFLow.pdf`. A few are explained below:
* `MessagesToSend/LINE_Waterway_Deschutes.kml` - a 'kml' file from Google Earth, used to define the line search task.
* `MessagesToSend/KmlToBoundariesTasks.WaterwaySearch.py` - a python script that process the kml file and generates LMCP messages for the example. 


## Running the Example:
1. open a ternimal window in the directory: "examples/05_Example_OffRoadAttack/"
2. enter the command: `./runAMASE_WaterwaySearch.sh`
3. start the Amase simulation (i.e. push the play button)
4. open another ternimal window in the directory: "examples/05_Example_OffRoadAttack/"
5. enter the command: `./runUxAS_WaterwaySearch_OffRoadAttack.sh`


### What Happens?
* When the Amase simulation starts, two UAVs will be initialized and begin loitering about to different loactions. Note: Amase uses NASA Worldwind for background imagery. If no imagery is available, Amase's background will be black.
* .3 seconds after UxAS starts a line representing the LineSearchTask will appear in Amase
* 5 seconds after UxAS start an AutomationRequest is sent to UxAS which kick off the mission
* Once the plans have been calculated and a UAV is assigned to perform the LineSearchTask, waypoints will be displayed in Amase and the UAV will start following them.
* When the UAV reaches the first waypoint of the LineSearchTask, its sensor will move to follow the river.
* At 40 second, the UAV violates the planned route and start to go another position which is not planned.

## Running the Example:
1. open a ternimal window in the directory: "examples/05_Example_OffRoadAttack/"
2. enter the command: `./runAMASE_WaterwaySearch.sh`
3. start the Amase simulation (i.e. push the play button)
4. open another ternimal window in the directory: "examples/05_Example_OffRoadAttack/"
5. enter the command: `./runUxAS_WaterwaySearch_BackToBeginAttack.sh`


### What Happens?
* At 40 second, the UAV violates the planned route and start to go back to the start position which is not planned.
