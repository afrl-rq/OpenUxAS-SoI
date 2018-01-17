#! /usr/bin/env python

import xml.dom.minidom
from xml.dom.minidom import Node
import pandas as pd
import glob
import math
import LocalCoords  # Conversion module

try:
    reload  # Python 2.7
except NameError:
    try:
        from importlib import reload  # Python 3.4+
    except ImportError:
        from imp import reload  # Python 3.0 - 3.3

def ProcessZone(zoneElement, zoneType):
    """	
	Return zoneID, label, zoneType, and boundary points for a CMASI AbstractZone.
	
	:param zoneElement: An xml.dom.minidom element representing a CMASI AbstractZone message.
	:param zoneType: A string describing the type of AbstractZone this message implements.
	:return: A list [zoneID, label, zoneType, boundaryPd], where zoneID is an int, label is a string, 
	         zoneType is the same as the input parameter, and boundaryPd is a pandas.DataFrame containing columns
	         of ['latitude','longitude','altitude'] values that define the zone boundary. In practice, a zone
	         boundary extends from MinAltitude to MaxAltitude. The data portion of boundaryPd defaults 
	         to an Empty Dataframe if a boundary element is not found in zoneElement.
	"""
    zoneID = 0
    elements = zoneElement.getElementsByTagName('ZoneID')
    if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
        zoneID = int(elements[0].firstChild.data)
    print('zoneID[' + str(zoneID) + ']')
    elements = zoneElement.getElementsByTagName('Label')
    if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
        label = str(elements[0].firstChild.data)
    else:
        label = str(zoneID)
    print('label[' + str(label) + ']')
    boundaryPoints = []
    boundaryElements = zoneElement.getElementsByTagName('Boundary')
    if boundaryElements:
        boundaryPoints = ProcessAbstractGeometry(boundaryElements[0])
    if not boundaryPoints:
        print('Missing boundary for zoneID[' + str(zoneID) + ']')
    boundaryPd = pd.DataFrame(data=boundaryPoints, columns=['latitude', 'longitude', 'altitude'])
    return [zoneID, label, zoneType, boundaryPd]


def ProcessAbstractGeometry(geometryElement):
    """
	Return boundary points for a CMASI AbstractGeometry message.
	
	:param geometryElement: An xml.dom.minidom element representing a CMASI AbstractGeometry message.
	:return: A list containing [lat, long, alt] elements that define the boundary. If the boundary
             cannot be constructed, returns an empty list.
	"""
    boundaryPoints = []
    circleElements = geometryElement.getElementsByTagName('Circle')
    polygonElements = geometryElement.getElementsByTagName('Polygon')
    rectangleElements = geometryElement.getElementsByTagName('Rectangle')
    if circleElements:
        loc3D = []
        radius = []
        centerPointElements = circleElements[0].getElementsByTagName('CenterPoint')
        if centerPointElements:
            location3DElements = centerPointElements[0].getElementsByTagName('Location3D')
            if location3DElements:
                loc3D = ProcessLocation3DElement(location3DElements[0])
        radiusElements = circleElements[0].getElementsByTagName('Radius')
        if radiusElements and radiusElements[0].firstChild and radiusElements[0].firstChild.nodeType == Node.TEXT_NODE:
            radius = float(radiusElements[0].firstChild.data)
        if type(radius) != float or len(loc3D) != 3:
            return []
        reload(LocalCoords)  # reset the initialization coordinates
        centerNorthEast_m = LocalCoords.LatLong_degToNorthEast_m(loc3D[0], loc3D[1])
        heading = 0;
        headingStep = math.pi / 18;  # 10 deg steps
        while heading < 2.0 * math.pi:
            north_m = radius * math.sin(heading) + centerNorthEast_m[0]
            east_m = radius * math.cos(heading) + centerNorthEast_m[1]
            boundaryPointLatLong = LocalCoords.NorthEast_mToLatLong_deg(north_m, east_m)
            boundaryPoints.append([boundaryPointLatLong[0], boundaryPointLatLong[1], loc3D[2]])
            heading = heading + headingStep
    elif polygonElements:
        boundaryPointElements = polygonElements[0].getElementsByTagName('BoundaryPoints')
        if boundaryPointElements:
            location3DElements = boundaryPointElements[0].getElementsByTagName('Location3D')
            for location3DElement in location3DElements:
                loc = ProcessLocation3DElement(location3DElement)
                if loc:
                    boundaryPoints.append(loc)
    elif rectangleElements:
        loc3D = []
        width = []
        height = []
        rotation = []
        centerPointElements = rectangleElements[0].getElementsByTagName('CenterPoint')
        if centerPointElements:
            location3DElements = centerPointElements[0].getElementsByTagName('Location3D')
            if location3DElements:
                loc3D = ProcessLocation3DElement(location3DElements[0])
        elements = rectangleElements[0].getElementsByTagName('Width')
        if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
            width = float(elements[0].firstChild.data)
        elements = rectangleElements[0].getElementsByTagName('Height')
        if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
            height = float(elements[0].firstChild.data)
        elements = rectangleElements[0].getElementsByTagName('Rotation')
        if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
            rotation = float(elements[0].firstChild.data)
        if type(width) != float or type(height) != float or type(rotation) != float or len(loc3D) != 3:
            return []
        reload(LocalCoords)  # reset the initialization coordinates
        centerNorthEast_m = LocalCoords.LatLong_degToNorthEast_m(loc3D[0], loc3D[1])
        boundaryPointsNorthEast = []
        boundaryPointsNorthEast.append([centerNorthEast_m[0] + height / 2, centerNorthEast_m[1] - width / 2])
        boundaryPointsNorthEast.append([centerNorthEast_m[0] + height / 2, centerNorthEast_m[1] + width / 2])
        boundaryPointsNorthEast.append([centerNorthEast_m[0] - height / 2, centerNorthEast_m[1] + width / 2])
        boundaryPointsNorthEast.append([centerNorthEast_m[0] - height / 2, centerNorthEast_m[1] - width / 2])
        for point in boundaryPointsNorthEast:
            north_m = math.cos(rotation * math.pi / 180.0) * point[0] - math.sin(rotation * math.pi / 180.0) * point[1]
            east_m = math.sin(rotation * math.pi / 180.0) * point[0] + math.cos(rotation * math.pi / 180.0) * point[1]
            boundaryPointLatLong = LocalCoords.NorthEast_mToLatLong_deg(north_m, east_m)
            boundaryPoints.append([boundaryPointLatLong[0], boundaryPointLatLong[1], loc3D[2]])
    else:
        print('ERROR:: Unknown boundary area type encountered!!!')
    return boundaryPoints


def ProcessLocation3DElement(Location3DElement):
    """
    Return a list [latitude, longitude, altitude] representing the value of a CMASI Location3D message.
    :param Location3DElement: An xml.dom.minidom element representing a CMASI Location3D message.
    :return: [latitude, longitude, altitude] if the message can be fully processed, [] otherwise.
    """
    loc3D = []
    elements = Location3DElement.getElementsByTagName('Latitude')
    if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
        loc3D.append(float(elements[0].firstChild.data))
    elements = Location3DElement.getElementsByTagName('Longitude')
    if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
        loc3D.append(float(elements[0].firstChild.data))
    elements = Location3DElement.getElementsByTagName('Altitude')
    if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
        loc3D.append(float(elements[0].firstChild.data))
    if len(loc3D) == 3:
        return loc3D
    else:
        return []


def ProcessZoneFile(filename):
    zones = []
    doc2 = xml.dom.minidom.parse(filename)
    if doc2.hasChildNodes():
        isGoodMessage = True
        zoneNode = doc2.firstChild
        zoneType = ''
        if str(zoneNode.nodeName) == 'KeepInZone':
            zoneType = 'KeepInZone'
        elif str(zoneNode.nodeName) == 'KeepOutZone':
            zoneType = 'KeepOutZone'
        else:
            print('ERROR:: Unknown zone type[' + str(zoneNode.nodeName) + '] encountered!!!')
            isGoodMessage = False
        if isGoodMessage:
            zones.append(ProcessZone(zoneNode, zoneType))
    return zones


def main():
    zoneArray = []
    for zoneFile in glob.glob('ZoneKeep*'):
        print('loading [' + zoneFile + ']')
        zoneArray.extend(ProcessZoneFile(zoneFile))
    zoneArrayPd = pd.DataFrame(data=zoneArray, columns=['zoneID', 'label', 'zoneType', 'boundaryPd'])
    print('saving [Zones.pkl]')
    zoneArrayPd.to_pickle('Zones.pkl')


if __name__ == '__main__':
    main()
