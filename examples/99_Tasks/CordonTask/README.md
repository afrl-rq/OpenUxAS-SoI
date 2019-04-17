Cordon Task
=======================

A task for using multiple ground vehicles to block access to an area. Given a point to secure and a standoff distance, task identifies number (K) routes that must be blocked to successfully deny access to the area.

Files:
------

* `cfg_CordonTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_CordonTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `MessagesToSend/` - Contains the messages send by UxAS with the send messages service.
* `MessagesToSend/GroundVehicleConfiguration_13.xml` - Details for ground vehicle 13.
* `MessagesToSend/GroundVehicleState_13.xml` - Ground vehicle 13's initial state.
* `MessagesToSend/GroundVehicleConfiguration_14.xml` - Details for ground vehicle 14.
* `MessagesToSend/GroundVehicleState_14.xml` - Ground vehicle 14's initial state.
* `MessagesToSend/GroundVehicleConfiguration_15.xml` - Details for ground vehicle 15.
* `MessagesToSend/GroundVehicleState_15.xml` - Ground vehicle 15's initial state.
* `MessagesToSend/GroundVehicleConfiguration_16.xml` - Details for ground vehicle 16.
* `MessagesToSend/GroundVehicleState_16.xml` - Ground vehicle 16's initial state.
* `MessagesToSend/CordonTask_100.xml` - The Cordon task.
* `MessagesToSend/AutomationRequest_CordonTask.xml` - The automation request for the Cordon task.
* `MessagesToSend/Pensacola_Map.xml` - The details of Pensacola.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/CordonTask"
2. enter the command `python3 runUxAS_CordonTask.py` or `./runUxAS_CordonTask.py`
3. start the AMASE simulation (i.e. press the play button)
