Multi-Vehicle Watch Task
=======================

A multi-vehicle overwatch task. Multiple vehicles will begin following and watching the desired vehicle.

Files:
------

* `cfg_MultiVehicleWatchTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_MultiVehicleWatchTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_MultiVehicleWatchTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_MultiVehicleWatchTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages send by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/AirVehicleConfiguration_V102.xml` - Details for air vehicle 102.
* `MessagesToSend/AirVehicleState_V102.xml` - Air vehicle 102's initial state.
* `MessagesToSend/AirVehicleConfiguration_V103.xml` - Details for air vehicle 103.
* `MessagesToSend/AirVehicleState_V103.xml` - Air vehicle 103's initial state.
* `MessagesToSend/MultiVehicleWatchTask_100.xml` - The multi-vehicle watch task that requests a watch of vehicle 103.
* `MessagesToSend/AutomationRequestMultiVehicleWatch.xml.xml` - The automation request for the multi-vehicle watch task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/MultiVehicleWatchTask"
2. enter the command `python3 runUxAS_MultiVehicleWatchTask.py` or `./runUxAS_MultiVehicleWatchTask.py`
3. open another terminal window in the directory: "examples/tasks/MultiVehicleWatchTask"
4. enter the command `python3 runAMASE_MultiVehicleWatchTask.py` or `./runAMASE_MultiVehicleWatchTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicles 101, 102, and 103 will be initialized and begin flying east.
* After 4 seconds, an automation request for the multi-vehicle watch task is sent.
* Once plans have been calculated, vehicles 101 and 102 will begin watching vehicle 103.
