Must Fly Task
=======================

A task that requires a vehicle to fly to a point with optional actions.

Files:
------

* `cfg_MustFlyTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_MustFlyTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_MustFlyTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_MustFlyTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages send by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/MustFlyTask_100.xml` - The requested must fly task.
* `MessagesToSend/AutomationRequest_MustFly.xml` - The automation request for the must fly task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/MustFlyTask"
2. enter the command `python3 runUxAS_MustFlyTask.py` or `./runUxAS_MustFlyTask.py`
3. open another terminal window in the directory: "examples/tasks/MustFlyTask"
4. enter the command `python3 runAMASE_MustFlyTask.py` or `./runAMASE_MustFlyTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicle 101 will be initialized and begin flying east.
* After 4 seconds, an automation request for the must fly task is sent.
* Once plans have been calculated, vehicle 101 will being performing the must fly task.
