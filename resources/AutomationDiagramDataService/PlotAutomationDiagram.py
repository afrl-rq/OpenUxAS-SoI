#! /usr/bin/env python

import pandas as pd
import os	#os.path.exists
import matplotlib
import matplotlib.pyplot as plt
import matplotlib.mlab as mlab
from matplotlib.backends.backend_pdf import PdfPages
from matplotlib.dates import YEARLY, DateFormatter, rrulewrapper, RRuleLocator, drange
import matplotlib.patches as mpatches
from itertools import cycle 
import LocalCoords	# lat/long conversion
import ProcessTasks	# process task messages
import ProcessUniqueAutomationResponse	# process UniqueAutomationResponse message
import ProcessEntityStates	# process vehicle states
import ProcessZones	# process keep-in/out zones

def main():

	print('')	# add a line return
	print('*** LOADING pkls ***')
	print('')	# add a line return

	tasksPickle = 'Tasks.pkl'			
	if not os.path.exists(tasksPickle):
		ProcessTasks.main()
	tasksPd = pd.read_pickle(tasksPickle)

	missionCommandPickle = 'MissionCommands.pkl'			
	if not os.path.exists(missionCommandPickle):
		ProcessUniqueAutomationResponse.main()
	missionCommandArrayPd = pd.read_pickle(missionCommandPickle)

	vehicleStatesPickle = 'VehicleStates.pkl'			
	if not os.path.exists(vehicleStatesPickle):
		ProcessEntityStates.main()
	vehicleStatesPd = pd.read_pickle(vehicleStatesPickle)

	zonesPickle = 'Zones.pkl'			
	if not os.path.exists(zonesPickle):
		ProcessZones.main()
	zoneArrayPd = pd.read_pickle(zonesPickle)

	print('')	# add a line return
	print('*** PLOTTING ***')
	print('')	# add a line return

	fig = plt.figure(10000)
	fig.clf()

	#############################################
	# the waypoint files
	plotLines = []
	labelStrings = []
	lastVehicleId = -1

	normVehicles = matplotlib.colors.Normalize(vmin=missionCommandArrayPd.vehicleID.min(), vmax=missionCommandArrayPd.vehicleID.max())
	cmapVehicles = matplotlib.cm.get_cmap('plasma')

	# THE PLANS/VEHICLES
	for missionCommand in missionCommandArrayPd.itertuples():
		vehicleID = missionCommand.vehicleID
		labelStrings.append(str(vehicleID))
		firstWaypoint = missionCommand.firstWaypoint
		commandID = missionCommand.commandID
		status = missionCommand.status
		vehicleColor = cmapVehicles(normVehicles(vehicleID))
		for vehicleState in vehicleStatesPd.itertuples():
			if vehicleID == vehicleState.vehicleID:
				# print('[' + str(vehicleState) + ']')
				vehicleLabel = 'V[' + str(vehicleState.vehicleID) + ']'
				labelStrings.append(vehicleLabel)
				NorthEast_m = LocalCoords.LatLong_degToNorthEast_m(vehicleState.latitude,vehicleState.longitude)
				plt.text(NorthEast_m[1],NorthEast_m[0],vehicleLabel,horizontalalignment='center',verticalalignment='top',color=[0.1,0.1,0.1],size=15)
				line, = plt.plot(NorthEast_m[1],NorthEast_m[0],'*',markersize=18,color=vehicleColor)
				plotLines.append(line)
				break;

		North_m = []
		East_m = []
		for waypoint in missionCommand.waypointListPd.itertuples():
			number = waypoint.number
			altitude = waypoint.altitude
			NorthEast_m = LocalCoords.LatLong_degToNorthEast_m(waypoint.latitude,waypoint.longitude)
			North_m.append(NorthEast_m[0])
			East_m.append(NorthEast_m[1])
			line, = plt.plot(NorthEast_m[1],NorthEast_m[0],'sg',markersize=5,color=vehicleColor)
			plotLines.append(line)
			# labelString = '[' + str(number) + ']'
			# plt.text(NorthEast_m[0],NorthEast_m[1],labelString,horizontalalignment='right',verticalalignment='top')
		line, = plt.plot(East_m,North_m,linestyle='-',color=vehicleColor)
		plotLines.append(line)
	# THE TASKS
	for task in tasksPd.itertuples():
		taskId = task.taskID
		taskLabel = task.label
		labelStrings.append(str(taskLabel))
		North_m = []
		East_m = []
		# print('task.searchBoundaryPd.size[' + str(task.searchBoundaryPd.size) + ']')
		if task.searchBoundaryPd.shape[0] != 1 and task.searchBoundaryPd.shape[0] != 0:
			for boundary in task.searchBoundaryPd.itertuples():
				NorthEast_m = LocalCoords.LatLong_degToNorthEast_m(boundary.latitude,boundary.longitude)
				North_m.append(NorthEast_m[0])
				East_m.append(NorthEast_m[1])
			plt.text(East_m[0],North_m[0],taskLabel,horizontalalignment='right',verticalalignment='top',color=[0.1,0.1,0.1],size=15)
			line, = plt.plot(East_m,North_m,linewidth=3,linestyle='--',color=[0.5,0.5,0.5])
			plotLines.append(line)
		elif task.searchBoundaryPd.shape[0] != 0:
			NorthEast_m = LocalCoords.LatLong_degToNorthEast_m(task.searchBoundaryPd.latitude[0],task.searchBoundaryPd.longitude[0])
			plt.text(NorthEast_m[1],NorthEast_m[0],taskLabel,horizontalalignment='right',verticalalignment='top',color=[0.1,0.1,0.1],size=15)
			line, = plt.plot(NorthEast_m[1],NorthEast_m[0],'o',markersize=12,color=[0.5,0.5,0.5])
			plotLines.append(line)
		else:
			print('Missing data: Could not plot task ' + taskLabel)
	# THE ZONES
	for zone in zoneArrayPd.itertuples():
		zoneId = zone.zoneID
		zoneLabel = zone.label
		labelStrings.append(str(zoneLabel))
		zoneColor = [0.1,0.1,0.1]
		zoneLineStyle = '-'
		zoneLinewidth = 1
		if zone.zoneType == 'KeepInZone':
			zoneColor = [0.4,0.4,0.4]
			zoneLineStyle = ':'
			zoneLinewidth = 4
		elif zone.zoneType == 'KeepOutZone':
			zoneColor = [0.1,0.1,0.1]
			zoneLineStyle = '-'
			zoneLinewidth = 4

		North_m = []
		East_m = []
		# print('zone.boundaryPd.size[' + str(zone.boundaryPd.shape) + ']')
		for boundary in zone.boundaryPd.itertuples():
			NorthEast_m = LocalCoords.LatLong_degToNorthEast_m(boundary.latitude,boundary.longitude)
			North_m.append(NorthEast_m[0])
			East_m.append(NorthEast_m[1])
		North_m.append(North_m[0])	#close the boundary
		East_m.append(East_m[0])
		plt.text(East_m[0],North_m[0],zoneLabel,horizontalalignment='right',verticalalignment='top',color=[0.1,0.1,0.1],size=15)
		line, = plt.plot(East_m,North_m,linewidth=zoneLinewidth,linestyle=zoneLineStyle,color=zoneColor)
		plotLines.append(line)

	#plt.title(stringTitle)
	plt.ylabel('postion north (m)')
	plt.xlabel('position east (m)')
	plt.grid(True)
	plt.axis('equal')
	# LEGEND STUFF
	# plt.legend(plotLines,labelStrings,shadow=True,fancybox=True,bbox_to_anchor=(0.9, 0.1), loc=2, borderaxespad=0.)
	# leg = plt.gca().get_legend()
	# ltext  = leg.get_texts()  # all the text.Text instance in the legend
	# llines = leg.get_lines()  # all the lines.Line2D instance in the legend
	# frame  = leg.get_frame()  # the patch.Rectangle instance surrounding the legend
	# frame.set_facecolor('0.80')      # set the frame face color to light gray
	# plt.setp(ltext, fontsize='small')    # the legend text fontsize
	# plt.setp(llines, linewidth=1.5)      # the legend linewidth
	#leg.draw_frame(False)           # don't draw the legend frame
	plt.draw()
	#save a pdf file
	pdfFileName = 'AutomationDiagram.pdf'
	pp = PdfPages(pdfFileName)
	pp.savefig()
	pp.close()
	plt.show()


if __name__ == '__main__':
    main()
