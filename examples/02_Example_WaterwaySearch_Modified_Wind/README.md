# Waterway Search Example

This is an example of running UxAS service that communicates to the Amase simulation in order to generate plans and an assignment for one of two UAVs to monitor a waterway. For more background see the file 'doc/UxAS_UserManual.pdf'

## Files:

* `cfg_WaterwaySearch.xml` - This is 
* `runUxAS_WaterwaySearch.sh` - 
* `runAMASE_WaterwaySearch.sh` - 
* `Scenario_WaterwaySearch.xml` -
* `MessagesToSend/` - most of the messages in this directory are explained in the document, `WaterwayExample_MessageFLow.pdf`. A few are explained below:
* `MessagesToSend/LINE_Waterway_Deschutes.kml` - a 'kml' file from Google Earth, used to define the line search task.
* `MessagesToSend/KmlToBoundariesTasks.WaterwaySearch.py` - a python script that process the kml file and generates LMCP messages for the example. 


## Running the Example:
1. open a ternimal window in the directory: "examples/02_Example_WaterwaySearch/"
2. enter the command: `./runAMASE_WaterwaySearch.sh`
3. start the Amase simulation (i.e. push the play button)
4. open another ternimal window in the directory: "examples/02_Example_WaterwaySearch/"
5. enter the command: `./runUxAS_WaterwaySearch.sh`


### What Happens?
* When the Amase simulation starts, two UAVs will be initialized and begin loitering about to different loactions. Note: Amase uses NASA Worldwind for background imagery. If no imagery is available, Amase's background will be black.
* .3 seconds after UxAS starts a line representing the LineSearchTask will appear in Amase
* 5 seconds after UxAS start an AutomationRequest is sent to UxAS which kick off the mission
* Once the plans have been calculated and a UAV is assigned to perform the LineSearchTask, waypoints will be displayed in Amase and the UAV will start following them.
* When the UAV reaches the first waypoint of the LineSearchTask, its sensor will move to follow the river.

### Things to Try:
1. Edit the file, 'Scenario_WaterwaySearch.xml' and change locations of the UAV so the assignment calculation produces different results.


