Watch Task
=======================

A task where a vehicle watches another vehicle.

Files:
------

* `cfg_WatchTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_WatchTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_WatchTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_WatchTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages sent by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V102.xml` - Details for air vehicle 102.
* `MessagesToSend/AirVehicleState_V102.xml` - Air vehicle 102's initial state.
* `MessagesToSend/AirVehicleConfiguration_V103.xml` - Details for air vehicle 103.
* `MessagesToSend/AirVehicleState_V103.xml` - Air vehicle 103's initial state.

* `MessagesToSend/WatchTask_100.xml` - The watch task configuration to watch vehicle 103.
* `MessagesToSend/AutomationRequest_WatchTask.xml` - The automation request for the watch task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/WatchTask/"
2. enter the command `python3 runUxAS_WatchTask.py` or `./runUxAS_WatchTask.py`
3. open another terminal window in the directory: "examples/tasks/Watch/"
4. enter the command `python3 runAMASE_WatchTask.py` or `./runAMASE_WatchTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicles 102 and 103 will be initialized and begin flying east.
* After 4 seconds, an automation request for the watch task is sent.
* Once plan has been calculated, vehicle 102 will begin watching vehicle 103.
