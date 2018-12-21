Blockade Task
=======================

A task for using multiple vehicles to surround an entity, for example, multiple vehicles surrounding an incoming enemy ship.

Files:
------

* `cfg_BlockadeTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_BlockadeTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_BlockadeTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_BlockadeTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages send by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/AirVehicleConfiguration_V102.xml` - Details for air vehicle 102.
* `MessagesToSend/AirVehicleState_V102.xml` - Air vehicle 102's initial state.
* `MessagesToSend/AirVehicleConfiguration_V103.xml` - Details for air vehicle 103.
* `MessagesToSend/AirVehicleState_V103.xml` - Air vehicle 103's initial state.
* `MessagesToSend/BlockadeTask_100.xml` - The blockade task that requests a blockade of vehicle 103.
* `MessagesToSend/AutomationRequest_Blockade.xml` - The automation request for the blockade task.
* `MessagesToSend/PointSearchTask_200` - The point search task that will be performed by vehicle 103.
* `MessagesToSend/AutomationRequest_PointSearch.xml` - The automation request for the point search task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/BlockadeTask"
2. enter the command `python3 runUxAS_BlockadeTask.py` or `./runUxAS_BlockadeTask.py`
3. open another terminal window in the directory: "examples/tasks/BlockadeTask"
4. enter the command `python3 runAMASE_BlockadeTask.py` or `./runAMASE_BlockadeTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicles 101, 102, and 103 will be initialized and begin flying east.
* After 1.5 seconds, an automation request for the point search task is sent.
* Once plans have been calculated, UAV 103 will being performing the point search task.
* After 9 seconds, an automation request for the blockade task is sent.
* Once plans have been calculated, vehicles 101 and 102 will begin the blockade task.
