Pattern Search Task
=======================

A task for performing a search pattern around a point.

Files:
------

* `cfg_PatternSearchTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_PatternSearchTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_PatternSearchTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_PatternSearchTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages sent by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/PatternSearchTask_100.xml` - The pattern search task configuration.
* `MessagesToSend/AutomationRequest_PatternSearch.xml` - The automation request for the pattern search task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/PatternSearchTask/"
2. enter the command `python3 runUxAS_PatternSearchTask.py` or `./runUxAS_PatternSearchTask.py`
3. open another terminal window in the directory: "examples/tasks/PatternSearchTask/"
4. enter the command `python3 runAMASE_PatternSearchTask.py` or `./runAMASE_PatternSearchTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicle 101 will be initialized and begin flying east.
* After 4 seconds, an automation request for the pattern search task is sent.
* Once plans have been calculated, UAV 101 will being performing the pattern search task.
