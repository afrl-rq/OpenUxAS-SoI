Rendezvous Task
=======================

A task that synchronizes all involved vehicles at a specified location (or set of locations) at the same time. Loiter patterns are used to ensure that when the latest vehicle arrives, the others will be in the proper positions and orientations to satisfy the location specification simultaneously.

Files:
------

* `cfg_RendezvousTask.xml` - The UxAS configuration file for this example. This configuration file sets up the services and bridges.
* `runUxAS_RendezvousTask.py` - This script runs UxAS with the details in the UxAS configuration file
* `runAMASE_RendezvousTask.py` - This script runs AMASE with the AMASE configuration file.
* `Scenario_RendezvousTask.xml` - The AMASE configuration file for this example.
* `MessagesToSend/` - Contains the messages sent by UxAS with the send messages service.
* `MessagesToSend/AirVehicleConfiguration_V101.xml` - Details for air vehicle 101.
* `MessagesToSend/AirVehicleState_V101.xml` - Air vehicle 101's initial state.
* `MessagesToSend/AirVehicleConfiguration_V102.xml` - Details for air vehicle 102.
* `MessagesToSend/AirVehicleState_V102.xml` - Air vehicle 102's initial state.
* `MessagesToSend/AirVehicleConfiguration_V103.xml` - Details for air vehicle 103.
* `MessagesToSend/AirVehicleState_V103.xml` - Air vehicle 103's initial state.
* `MessagesToSend/RendezvousTask_100.xml` - The rendezvous task configuration.
* `MessagesToSend/AutomationRequest_RendezvousTask.xml` - The automation request for the rendezvous task.


Running the example:
--------------------
1. Open a terminal window in the directory: "examples/tasks/RendezvousTask/"
2. enter the command `python3 runUxAS_RendezvousTask.py` or `./runUxAS_RendezvousTask.py`
3. open another terminal window in the directory: "examples/tasks/Rendezvous/"
4. enter the command `python3 runAMASE_RendezvousTask.py` or `./runAMASE_RendezvousTask.py`
5. start the AMASE simulation (i.e. press the play button)

### What happens?
* When the AMASE simulation starts, vehicles 101, 102, and 103 will be initialized and begin flying east.
* After 4 seconds, an automation request for the rendezvous task is sent.
* Once plans have been calculated, vehicles 101, 102, and 103 will being performing the rendezvous task.
