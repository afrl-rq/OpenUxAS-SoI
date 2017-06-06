#! /usr/bin/env python

import xml.dom.minidom
import pandas as pd
import glob
import math 	# pi
# import the conversion module
import LocalCoords


def ProcessZone(zoneNode,zoneType):
	# AbstractZone
	# ZoneID - A globally unique reference number for this zone
	# Label - Optional label for this zone
	# Boundary - Geometry object describing the boundary. This boundary is 2-dimensional. 
	#	The zone boundary is defined as an extrusion of this boundary from MinAltitude to MaxAltitude.

	zoneID = 0
	elements = zoneNode.getElementsByTagName('ZoneID')
	if len(elements):
		zoneID = int(elements[0].firstChild.data)
	print('zoneID[' + str(zoneID) + ']')
	label = ''
	elements = zoneNode.getElementsByTagName('Label')
	if len(elements):
		label = str(elements[0].firstChild.data)
	print('label[' + str(label) + ']')

	boundaryPoints = []
	boundaryNode = zoneNode.getElementsByTagName('Boundary')
	print('boundaryNode[' + str(boundaryNode[0].nodeName) + ']')
	if len(boundaryNode):
		circleNode = boundaryNode[0].getElementsByTagName('Circle')
		polygonNode = boundaryNode[0].getElementsByTagName('Polygon')
		rectangleNode = boundaryNode[0].getElementsByTagName('Rectangle')
		# print('boundaryNode[' + str(boundaryNode[0].firstChild) + ']')
		boundaryType = str('Circle')
		if len(circleNode):
			centerPointNode = circleNode[0].getElementsByTagName('CenterPoint')
			latitude = 0
			longitude = 0
			altitude = 0
			radius = 0
			if len(centerPointNode):
				location3DElements = centerPointNode[0].getElementsByTagName('Location3D')
				if location3DElements:
					elements = location3DElements[0].getElementsByTagName('Latitude')
					if elements:
						latitude = float(elements[0].firstChild.data)
					elements = location3DElements[0].getElementsByTagName('Longitude')
					if elements:
						longitude = float(elements[0].firstChild.data)
					elements = location3DElements[0].getElementsByTagName('Altitude')
					if elements:
						altitude = float(elements[0].firstChild.data)
			radiusNode = circleNode[0].getElementsByTagName('Radius')
			if len(radiusNode):
				radius = float(radiusNode[0].firstChild.data)
			reload(LocalCoords)		# reset the initialization coordinates
			centerNorthEast_m = LocalCoords.LatLong_degToNorthEast_m(latitude,longitude)
			heading = 0;
			headingStep = math.pi/18;	# 10 deg steps
			while heading < 2.0*math.pi:
				north_m = radius*math.sin(heading) + centerNorthEast_m[0] 
				east_m = radius*math.cos(heading) + centerNorthEast_m[1] 
				boundaryPointLatLong = LocalCoords.NorthEast_mToLatLong_deg(north_m,east_m)
				boundaryPoints.append([boundaryPointLatLong[0],boundaryPointLatLong[1],altitude])
				heading = heading + headingStep
		elif len(polygonNode):
			latitude = 0
			longitude = 0
			altitude = 0
			boundaryPointNodes = polygonNode[0].getElementsByTagName('BoundaryPoints')
			if len(boundaryPointNodes):
				location3DElements = boundaryPointNodes[0].getElementsByTagName('Location3D')
				for location3DElement in location3DElements:
					elements = location3DElement.getElementsByTagName('Latitude')
					if elements:
						latitude = float(elements[0].firstChild.data)
					elements = location3DElement.getElementsByTagName('Longitude')
					if elements:
						longitude = float(elements[0].firstChild.data)
					elements = location3DElement.getElementsByTagName('Altitude')
					if elements:
						altitude = float(elements[0].firstChild.data)
					boundaryPoints.append([latitude,longitude,altitude])
		elif len(rectangleNode):
			print('WARNING:: Rectangle boundary not implemented!!!')
		else:
			print('ERROR:: Unknown boundary area type[' + boundaryType +'] encountered!!!')
	boundaryPd = pd.DataFrame(data = boundaryPoints,columns=['latitude','longitude','altitude'])
	return [zoneID,label,zoneType,boundaryPd]


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
			print('ERROR:: Unknown zone type[' + str(zoneNode.nodeName) +'] encountered!!!')
			isGoodMessage = False
		if isGoodMessage:
			zones.append(ProcessZone(zoneNode,zoneType))
	return zones

def main():
	zoneArray = []
	for zoneFile in glob.glob('ZoneKeep*'):
		print('loading [' + zoneFile + ']')
		zoneArray.extend(ProcessZoneFile(zoneFile))
	zoneArrayPd = pd.DataFrame(data = zoneArray,columns=['zoneID','label','zoneType','boundaryPd'])
	print('saving [Zones.pkl]')
	zoneArrayPd.to_pickle('Zones.pkl')

if __name__ == '__main__':
    main()
