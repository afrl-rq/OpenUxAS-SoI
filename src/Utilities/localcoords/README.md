# LocalCoords Python Module

**DESCRIPTION:**

The LocalCoords module converts between Latitude/Longitude and North/East coordinates.
   - Latitude/Longitude coordinates are based on the WGS-84 ellipsoid
   - North/East coordinates are in a linear Cartesian coordinate system, tangent to the WGS-84
     ellipsoid at a given reference location (lat/long)

**INSTALLATION:**

To build/install with Python 2, run 'python setup.py install'

To build/install with Python 3, run 'python3 setup_py3.py install'

**USE:**

LocalCoords has three functions: Initialize_deg, LatLong_degToNorthEast_m, and NorthEast_mToLatLong_deg.

*Initialize_deg(Latitude_Init_deg,Longitude_Init_deg):*
   - This function sets the linearization point to the given
     latitude and longitude. Note: the linearization point is set by a call to Initialize_deg or
     LatLong_degToNorthEast_m, which ever comes first. It will not be reset by subsequent calls.
   - Returns: 0
	 
*LatLong_degToNorthEast_m(Latitude_deg,Longitude_deg):*
   - This function linearizes the given latitude and longitude
     about the linearization point. If the linearization point has not been set, a call to this function sets it.
   - Returns: North and East coordinates in meters
	 
*NorthEast_mToLatLong_deg(North_m,East_m):*
   - This function converts the given linear coordinates to latitude and longitude
     coordinates based on the linearization point. Note: if the linearization was not set before NorthEast_mToLatLong_deg
     is called then it is an error.
   - Returns: Latitude and Longitude coordinates in degrees

**EXAMPLE:**

```
# import the conversion module
import LocalCoords


#convert from lat long degrees to meters
#############################################

# the initial latitude and longitude (linearization point) is set during the first call to LocalCoords:
Latitude_Init_deg = 39.338760
Longitude_Init_deg = -86.027701
LinearCoordinates_Init = LocalCoords.LatLong_degToNorthEast_m(Latitude_Init_deg,Longitude_Init_deg)
print LinearCoordinates_Init

# subsequent calls are linerized using the inital point
Latitude_deg = 39.345334
Longitude_deg = -86.039201
LinearCoordinates_01 = LocalCoords.LatLong_degToNorthEast_m(Latitude_deg,Longitude_deg)
print LinearCoordinates_01

# subsequent calls are linerized using the inital point
Latitude_deg = 39.355334
Longitude_deg = -86.029201
LinearCoordinates_02 = LocalCoords.LatLong_degToNorthEast_m(Latitude_deg,Longitude_deg)
print LinearCoordinates_02

# the initial latitude and longitude (linearization point) is set during the first call to LocalCoords:
Latitude_Init_deg = 39.338760
Longitude_Init_deg = -86.027701
LinearCoordinates_Init = LocalCoords.LatLong_degToNorthEast_m(Latitude_Init_deg,Longitude_Init_deg)
print LinearCoordinates_Init

#############################################
#convert from meters to lat long degrees
#############################################
# the 'Initialize_deg' function can be used to set the linearization point
#     this makes it possible to convert from meters to lat/long without
#     converting from lat/long to meters first:
Latitude_Init_deg = 39.338760
Longitude_Init_deg = -86.027701
LinearCoordinates_Init = LocalCoords.Initialize_deg(Latitude_Init_deg,Longitude_Init_deg)
print LinearCoordinates_Init

# convert from meters to lat/long. It is an error if an linearization point has not been set before this call:
North_m = 0.0
East_m = 0.0
LatLongCoordinates_Init = LocalCoords.NorthEast_mToLatLong_deg(North_m,East_m)
print LatLongCoordinates_Init

# convert from meters to lat/long. It is an error if an linearization point has not been set before this call:
North_m = -991.4355630207798
East_m = 729.8580936967238
LatLongCoordinates_01 = LocalCoords.NorthEast_mToLatLong_deg(North_m,East_m)
print LatLongCoordinates_01

# convert from meters to lat/long. It is an error if an linearization point has not been set before this call:
North_m = -129.31768213333595
East_m = 1840.0772809452008
LatLongCoordinates_02 = LocalCoords.NorthEast_mToLatLong_deg(North_m,East_m)
print LatLongCoordinates_02

```
