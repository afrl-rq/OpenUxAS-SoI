# Hello World Example

This is a basic example of a UxAS service that sends/receives KeyValuePair messages and prints out the results. 

## Files:

    *runUxAS_HelloWorld.py* - This is a python script used to execute the example

    *runUxAS_HelloWorld_Docker.py* - This is a python script used to execute the example using Docker

    *runUxAS_HelloWorld.sh* - This is a bash shell script used to execute the example (deprecated)

    *cfg_HelloWorld.xml* - This is the file used to configure the example for UxAS

    *01_HelloWorld.cpp* - the C++ source code for the example. Note: this file is located in the following directory:
        src/Services/

    *01_HelloWorld.h* - the C++ header file for the example. Note: this file is located in the following directory:
        src/Services/

## Running the Example:
1. open a terminal window in the directory: "examples/01_HelloWorld/"
2. enter the command: `./runUxAS_HelloWorld.sh`

### What Happens?
Two copies of the HelloWorld service start up and begin sending messages. One copy sends a message once a second and the other sends a message every 5 seconds. Each service receives the messsages sent by the other service. When messages are received the services print them out.

### Things to Try:
1. Change the rate that messages are sent out. This is done by editing the `cfg_HelloWorld.xml` file and changing the value of `SendPeriod_ms`. Note: the time is entered in milliseconds, i.e. 1000 milliseconds == 1 second.
2. Change the message sent by each of the services. This is done by editing the `cfg_HelloWorld.xml` file and changing the value of `StringToSend`.

