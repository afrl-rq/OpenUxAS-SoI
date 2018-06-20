# Python AMASE Example

The purpose of this example is twofold: 

1. To show how to use Python with AMASE directly rather than through UxAS. 
2. To provide some standard configuration options for air vehicles and their payloads.

This example includes a Python program that connects to AMASE and sends the LMCP messages necessary to configure, initialize, and command a set of air vehicles. It then saves these messages as a scenario file `Scenario_Output.xml` that can be used to re-run the scenario in AMASE by itself. Finally, it receives information about the air vehicles from AMASE through LMCP messages and prints this information.

**Note**: this example is currently untested on Windows.



## Files:

* `RunPythonWithAmase.py` - Python program that sends and receives LMCP messages to/from AMASE.
* `Scenario_Empty.xml` - An AMASE scenario file that zooms in on the map but is otherwise empty.
* `runAMASE_PythonWithAmase.sh` - bash script to startup AMASE with the empty scenario.
* `runAMASE_PythonWithAmase.bat` - Windows script to startup AMASE with an empty scenario.
* `MessageLibrary/` - A collection of representative `AirVehicleConfiguration`, `AirVehicleState`, `GimbalConfiguration`, `GimbalState`, `CameraConfiguration`, `CameraState`, and `FlightProfile` messages that can be used to configure air vehicles and their payloads.




## Running the Example:
1. Open a terminal window in the directory: `examples/07_PythonWithAmase/`
2. Enter the command: `./runAMASE_PythonWithAmase.sh`
3. Start the AMASE simulation (i.e. push the play button)
4. Open another terminal window in the directory: `examples/07_PythonWithAmase/`
5. Enter the command: `python RunPythonWithAmase.py`


### What Happens?
* When the AMASE simulation starts, it is configured to set up a TCP/IP server on port 5555.
* When the Python program starts, it connects to the AMASE TCP/IP server using ZeroMQ.
* The Python program creates the LMCP messages necessary to configure and initialize three air vehicles in AMASE, some entirely from "stratch" and others by loading and modifying messages from the `MessageLibrary/` directory, and sends them to AMASE.
* The Python program then creates and sends some example `MissionCommand` and  `VehicleActionCommand` LMCP messages to control the vehicles.
* Then Python program then reads through queued LMCP messages until it reaches an `AirVehicleState` message that has a timestamp of at least 7000 ms into the scenario. It then prints out certain `AirVehicleState` information (ID, Time, Latitude, Longitude, Altitude, and EnergyAvailable) for each vehicle.

### Things to Try:
1. Running `RunPythonWithAmase.py` generates the file `Scenario_Output.xml`, which saves the messages it sends to AMASE in a 'scenario file.' Restart AMASE by following steps 1 and 2 above, then load this scenario file in AMASE by going to AMASE's `File > Open Scenario` menu and selecting `Scenario_Output.xml`. Then press the Play button in AMASE. AMASE should configure and command the air vehicles just as `RunPythonWithAmase.py` did.
2. Try to add a fourth air vehicle to the scenario in `RunPythonWithAmase.py` with different configuration and state information than the other three. Send it at least one `MissionCommand` and/or `VehicleActionCommand`.
