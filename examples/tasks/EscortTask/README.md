Escort Task
=======================

A task for targeting surveillance at an offset of a moving entity. This can be used to scout ahead or behind a convoy.

Files:
------

* `cfg_EscortTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_EscortTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_EscortTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_EscortTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages send by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/AirVehicleConfiguration_V102.xml` - Details for air vehicle 102.
* `MessagesToSend/AirVehicleState_V102.xml` - Air vehicle 102's initial state.
* `MessagesToSend/AirVehicleConfiguration_V103.xml` - Details for air vehicle 103.
* `MessagesToSend/AirVehicleState_V103.xml` - Air vehicle 103's initial state.
* `MessagesToSend/ImpactLineSearchTask_100.xml` - A line search task for vehicle 101 to perform.
* `MessagesToSend/AutomationRequest_LineSearchTask.xml` - The automation request for the line search task.
* `MessagesToSend/EscortTask_Ahead_200.xml` - A task to escort ahead of air vehicle 101.
* `MessagesToSend/AutomationRequest_EscortTask_Ahead.xml` - The automation request for the escort ahead task.
* `MessagesToSend/EscortTask_Ahead_300.xml` - A task to escort behind air vehicle 101.
* `MessagesToSend/AutomationRequest_EscortTask_Behind.xml` - The automation request for the escort behind task.



Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/EscortTask"
2. enter the command `python3 runUxAS_EscortTask.py` or `./runUxAS_EscortTask.py`
3. open another terminal window in the directory: "examples/tasks/EscortTask"
4. enter the command `python3 runAMASE_EscortTask.py` or `./runAMASE_EscortTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicles 101, 102, and 103 will be initialized and begin flying east.
* After 1.5 seconds, an automation request for the point search task is sent.
* Once plan have been calculated, UAV 103 will being performing the point search task.
* After 9 seconds, an automation request for the Escort task is sent.
* Once plans have been calculated, vehicles 101 and 102 will begin the Escort task.
