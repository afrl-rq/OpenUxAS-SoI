#! /usr/bin/env python

import xml.dom.minidom
from xml.dom.minidom import Node
import pandas as pd
import glob

def get_a_document(filename):
    return xml.dom.minidom.parse(filename)

def ProcessMissionCommand(missionCommand):
	isGoodMessage = True
	try:
		firstWaypoint = 0
		elements = missionCommand.getElementsByTagName('FirstWaypoint')
		if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
			firstWaypoint = int(elements[0].firstChild.data)

		commandID = 0
		elements = missionCommand.getElementsByTagName('CommandID')
		if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
			commandID = int(elements[0].firstChild.data)

		vehicleID = 0
		elements = missionCommand.getElementsByTagName('VehicleID')
		if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
			vehicleID = int(elements[0].firstChild.data)

		status = 'Cancelled'
		elements = missionCommand.getElementsByTagName('Status')
		if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
			status = str(elements[0].firstChild.data)

		waypointList = []
		elements = missionCommand.getElementsByTagName('WaypointList')
		if elements:
			elementWaypoints = elements[0].getElementsByTagName('Waypoint')
			for elementWaypoint in elementWaypoints:
				number = -1
				elements1 = elementWaypoint.getElementsByTagName('Number')
				if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
					number = int(elements1[0].firstChild.data)
				altitude = -1
				elements1 = elementWaypoint.getElementsByTagName('Altitude')
				if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
					altitude = float(elements1[0].firstChild.data)
				latitude = 0
				elements1 = elementWaypoint.getElementsByTagName('Latitude')
				if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
					latitude = float(elements1[0].firstChild.data)
				elements1 = elementWaypoint.getElementsByTagName('Longitude')
				longitude = 0
				if elements and elements[0].firstChild and elements[0].firstChild.nodeType == Node.TEXT_NODE:
					longitude = float(elements1[0].firstChild.data)
				waypointList.append([number,latitude,longitude,altitude])
				# print('# 5a status[' + str(waypointList) + ']')
		waypointListPd = pd.DataFrame(data = waypointList,columns=['number','latitude','longitude','altitude'])

	except StandardError:
		print('### Error encountered while processing the MissionCommand ###')
		isGoodMessage = False
	except:
		print('### Error encountered while processing the MissionCommand ###Unexpected error:', sys.exc_info()[0])
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
		print('loading [' + AutomationResponseFile + ']')
		missionCommandArray = ProcessAutomationResponseFile(AutomationResponseFile)
	missionCommandArrayPd = pd.DataFrame(data = missionCommandArray,columns=['vehicleID','firstWaypoint','commandID','status','waypointListPd'])
	print('saving [MissionCommands.pkl]')
	missionCommandArrayPd.to_pickle('MissionCommands.pkl')

if __name__ == '__main__':
    main()
