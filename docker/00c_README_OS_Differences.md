# Operating System Differences

## Overview
As we discover them, we will document import differences
  in how Docker operates on different operating systems.


## Container/Host Network Communications
Docker has implemented a powerful set of network communication
implementations that facilitate connecting containers and services.
Unfortunately, communications from inside containers to host applications
are implemented differently on LINUX, Windows, and MACOS. This means
that communincation between UxAS, inside a container, and AMASE running 
on a host system is implemented differently for each of these OS's.

- `LINUX OS` the simplest method to communicate from inside the container
to the host, and beyond, with LINUX is the use the option, `--network 
host`, when creating the Docker container. This maps the host network 
to the container network. This makes it possible to run UxAS as if it 
was not inside a Docker container, for example, the network device can 
be accessed by Zyre to broadcast heartbeats.

- `Windows OS` this implementation uses a `bridge` network for communication
from the container to the host. The host ports are only accessable to the 
applications in the container through the `gateway` IP address on the `bridge`.
To find the `gateway` IP address:
  -- open the Docker settings: Open the Docker for Windows menu by right-
  clicking the Docker icon in the Notifications area (or System tray), Select 
  `Settings`. 
  -- select the `Network` tab (on the left side of the dialog window)
  -- use the `Internal Virtual Switch` `Subnet Address` and change the
  last octet to 1. For example if the subnet addrees is 10.0.75.0, then 
  the `gateway` IP address is 10.0.75.1
 To configure communcation between containerized UxAS and AMASE use an 
 address such as `tcp://10.0.75.1:5555`

 - `MACOS` this implementation does not connect direcly to a bridge which
 make finding the required `gateway` address difficult. So far, the best
 way that I have discovered to find the `gateway` address is to look it up
 using the special Docker address, `host.docker.internal`, and a simple 
 Docker container, for example:
  docker run --rm alpine nslookup host.docker.internal
 In this case, my returned address was `192.168.65.2` and the address used
 to communicate with AMASE was `192.168.65.2:5555` 

 NOTE: At this point, I have not been able to access the network `device` 
 directly inside the containers on Windows and MACOS. So at this point 
 Zyre won't be able to send out broadcast heartbeats and thus will not 
 operate correctly.

 Zyre does work from inside the LINUX containers.

 NOTE: firewalls can block communication between applications in containers
 and those running on the host