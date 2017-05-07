#! /usr/bin/env python

import xml.dom.minidom
import pandas as pd
import glob
import math 	# pi
# import the conversion module
import LocalCoords

def ProcessEntityStateFile(filename):

	isGoodMessage = True
	entityState = []
	doc2 = xml.dom.minidom.parse(filename)
	if doc2.hasChildNodes():
		try:
			entityId = 0
			elements = doc2.getElementsByTagName('ID')
			if len(elements):
				entityId = long(elements[0].firstChild.data)
			latitude = 0.0
			longitude = 0.0
			altitude = 0.0
			elements = doc2.getElementsByTagName('Location')
			if len(elements):
				locationNode = elements[0].getElementsByTagName('Location3D')
				if len(locationNode):
					elements = locationNode[0].getElementsByTagName('Latitude')
					if elements:
						latitude = float(elements[0].firstChild.data)
					elements = locationNode[0].getElementsByTagName('Longitude')
					if elements:
						longitude = float(elements[0].firstChild.data)
					elements = locationNode[0].getElementsByTagName('Altitude')
					if elements:
						altitude = float(elements[0].firstChild.data)
			heading = 0
			elements = doc2.getElementsByTagName('Heading')
			if len(elements):
				heading = float(elements[0].firstChild.data)

		except StandardError:
			print '### Error encountered while processing the EnityState ###'
			isGoodMessage = False
		except:
			print '### Error encountered while processing the EnityState ###Unexpected error:', sys.exc_info()[0]
			isGoodMessage = False
	if isGoodMessage:
		return [entityId,latitude,longitude,altitude,heading]

	return entityState

def main():
	vehicleStateArray = []
	for entityStateFile in glob.glob('EnityState_Id*'):
		print 'loading [' + entityStateFile + ']'
		vehicleStateArray.append(ProcessEntityStateFile(entityStateFile))
	vehicleStatesPd = pd.DataFrame(data = vehicleStateArray,columns=['vehicleID','latitude','longitude','altitude','heading'])
	print 'saving [VehicleStates.pkl]'
	vehicleStatesPd.to_pickle('VehicleStates.pkl')

if __name__ == '__main__':
    main()
