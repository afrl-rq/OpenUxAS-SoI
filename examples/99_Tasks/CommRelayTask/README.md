Communication Relay Task
=======================

A task for providing communication relay support.

Files:
------

* `cfg_CommRelayTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_CommRelayTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_CommRelayTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_CommRelayTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages send by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/AirVehicleConfiguration_V102.xml` - Details for air vehicle 102.
* `MessagesToSend/AirVehicleState_V102.xml` - Air vehicle 102's initial state.
* `MessagesToSend/RadioTowerConfiguration_V21.xml` - Details for radio tower 21.
* `MessagesToSend/RadioTowerState_V21.xml` - Radio tower 21's initial state.
* `MessagesToSend/CommRelayTask_100.xml` - The comm relay task to support vehicle 101.
* `MessagesToSend/AutomationRequest_CommRelay.xml` - The automation request for the communication relay task.
* `MessagesToSend/PointSearchTask_200.xml` - The point search task.
* `MessagesToSend/AutomationRequest_PointSearch.xml` - The automation request for the line search task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/CommRelayTask"
2. enter the command `python3 runUxAS_CommRelayTask.py` or `./runUxAS_CommRelayTask.py`
3. open another terminal window in the directory: "examples/tasks/CommRelayTask"
4. enter the command `python3 runAMASE_CommRelayTask.py` or `./runAMASE_CommRelayTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicles 101 and 102 will be initialized and begin flying east.
* After 1.5 seconds, an automation request for the point search task is sent.
* Once plans have been calculated, vehicle 101 will being performing the point search task.
* After 6 seconds, an automation request for the communication relay task is sent.
* Once the task has been calculated, vehicle 102 will begin performing the communication relay task.
