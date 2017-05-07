#! /usr/bin/env python

import xml.dom.minidom
import pandas as pd
import glob

def get_a_document(filename):
    return xml.dom.minidom.parse(filename)

def ProcessMissionCommand(missionCommand):
	isGoodMessage = True
	try:
		firstWaypoint = 0
		elements = missionCommand.getElementsByTagName('FirstWaypoint')
		if len(elements):
			firstWaypoint = long(elements[0].firstChild.data)

		commandID = 0
		elements = missionCommand.getElementsByTagName('CommandID')
		if len(elements):
			commandID = long(elements[0].firstChild.data)

		vehicleID = 0
		elements = missionCommand.getElementsByTagName('VehicleID')
		if len(elements):
			vehicleID = long(elements[0].firstChild.data)

		status = 'Cancelled'
		elements = missionCommand.getElementsByTagName('Status')
		if len(elements):
			status = str(elements[0].firstChild.data)

		waypointList = []
		elements = missionCommand.getElementsByTagName('WaypointList')
		if len(elements):
			elementWaypoints = elements[0].getElementsByTagName('Waypoint')
			for elementWaypoint in elementWaypoints:
				number = -1
				elements1 = elementWaypoint.getElementsByTagName('Number')
				if len(elements1):
					number = long(elements1[0].firstChild.data)
				altitude = -1
				elements1 = elementWaypoint.getElementsByTagName('Altitude')
				if len(elements1):
					altitude = float(elements1[0].firstChild.data)
				latitude = 0
				elements1 = elementWaypoint.getElementsByTagName('Latitude')
				if len(elements1):
					latitude = float(elements1[0].firstChild.data)
				elements1 = elementWaypoint.getElementsByTagName('Longitude')
				longitude = 0
				if len(elements1):
					longitude = float(elements1[0].firstChild.data)
				waypointList.append([number,latitude,longitude,altitude])
				# print '# 5a status[' + str(waypointList) + ']'
		waypointListPd = pd.DataFrame(data = waypointList,columns=['number','latitude','longitude','altitude'])

	except StandardError:
		print '### Error encountered while processing the MissionCommand ###'
		isGoodMessage = False
	except:
		print '### Error encountered while processing the MissionCommand ###Unexpected error:', sys.exc_info()[0]
		isGoodMessage = False
	if isGoodMessage:
		return [vehicleID,firstWaypoint,commandID,status,waypointListPd]

def ProcessAutomationResponseFile(filename):
	doc2 = get_a_document(filename)

	originalResponse = doc2.getElementsByTagName('OriginalResponse')
	automationResponse = originalResponse[0].getElementsByTagName('AutomationResponse')
	missionCommandList = automationResponse[0].getElementsByTagName('MissionCommandList')
	missionCommands = missionCommandList[0].getElementsByTagName('MissionCommand')
	missionCommandArray = []
	for missionCommand in missionCommands:
		missionCommandArray.append(ProcessMissionCommand(missionCommand))
	return missionCommandArray 

def main():
	missionCommandArray = []
	for AutomationResponseFile in glob.glob('UniqueAutomationResponse*'):
		print 'loading [' + AutomationResponseFile + ']'
		missionCommandArray = ProcessAutomationResponseFile(AutomationResponseFile)
	missionCommandArrayPd = pd.DataFrame(data = missionCommandArray,columns=['vehicleID','firstWaypoint','commandID','status','waypointListPd'])
	print 'saving [MissionCommands.pkl]'
	missionCommandArrayPd.to_pickle('MissionCommands.pkl')

if __name__ == '__main__':
    main()
