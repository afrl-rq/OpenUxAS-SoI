Loiter Task
=======================

An task where a vehicle loiters around a point.

Files:
------

* `cfg_LoiterTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_LoiterTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_LoiterTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_LoiterTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages sent by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/LoiterTask_100.xml` - The loiter task that is requested.
* `MessagesToSend/AutomationRequest_LoiterTask.xml` - The automation request for the loiter task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/LoiterTask"
2. enter the command `python3 runUxAS_LoiterTask.py` or `./runUxAS_LoiterTask.py`
3. open another terminal window in the directory: "examples/tasks/LoiterTask"
4. enter the command `python3 runAMASE_LoiterTask.py` or `./runAMASE_LoiterTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicle 101 will be initialized and begin flying east.
* After 4 seconds, an automation request for the loiter task is sent.
* Once plans have been calculated, vehicle 101 will being performing the loiter task.
