#!/usr/bin/env python

import os
from lxml import etree
import pandas as pd
import glob
import re



def SaveBoundaryToPcc(file,id,boundaryName,boundaryType,coordinatesPd):
	file.write('<Boundary>\n')
	file.write('<Name>{0} (ID-{2}, {1})</Name>\n'.format(boundaryName,boundaryType,id))
	file.write('<Description></Description>\n')
	file.write('<Range MaxValue="0" MinValue="0" />\n')
	file.write('<ExtendToGnd>0</ExtendToGnd>\n')
	file.write('<Alarm>0</Alarm>\n')
	file.write('<BoundaryMetaData>\n')
	if 'Zone' in boundaryType:
		file.write('<LineColor Blue="255" Red="51" Green="0" />\n')
		file.write('<FillColor Blue="255" Red="51" Green="0" />\n')
		file.write('<LineWidth>4</LineWidth>\n')
		file.write('<LineOpacity>1</LineOpacity>\n')
		file.write('<FillOpacity>.2</FillOpacity>\n')
		file.write('<FillTop>1</FillTop>\n')
	else:
		#set up for road
		file.write('<LineColor Blue="0" Red="0" Green="0" />\n')
		file.write('<FillColor Blue="0" Red="0" Green="0" />\n')
		file.write('<LineWidth>4</LineWidth>\n')
		file.write('<LineOpacity>1</LineOpacity>\n')
		file.write('<FillOpacity>0</FillOpacity>\n')
		file.write('<FillTop>0</FillTop>\n')

	file.write('<Editable>0</Editable>\n')
	file.write('<Visible>1</Visible>\n')
	file.write('</BoundaryMetaData>\n')
	file.write('<VertexList>\n')
	for coordinate in coordinatesPd.itertuples():
		file.write('\t<LatLonAlt>\n\t\t<LatitudeDeg>{0}</LatitudeDeg>\n\t\t<LongitudeDeg>{1}</LongitudeDeg>\n\t\t<AltitudeMeters>{2}</AltitudeMeters>\n\t\t<AltitudeType>3</AltitudeType>\n\t</LatLonAlt>\n'.
		format(coordinate.latitude,coordinate.longitude,coordinate.altitude))
	if 'LineSearch' in boundaryType:
		coordinatesPdRev = coordinatesPd.reindex(index=coordinatesPd.index[::-1])
		for coordinate in coordinatesPdRev.itertuples():
			file.write('\t<LatLonAlt>\n\t\t<LatitudeDeg>{0}</LatitudeDeg>\n\t\t<LongitudeDeg>{1}</LongitudeDeg>\n\t\t<AltitudeMeters>{2}</AltitudeMeters>\n\t\t<AltitudeType>3</AltitudeType>\n\t</LatLonAlt>\n'.
			format(coordinate.latitude,coordinate.longitude,coordinate.altitude))
	file.write('\t</VertexList>\n')
	file.write('</Boundary>\n')

def SaveProceedToPointAndHoldTask(pathSave,taskId,taskName,point):
	fileName = '{0:4d}_ImpactPointSearchTask_{1}.xml'.format(taskId,taskName)
	strPathFileSave = pathSave + fileName
	xf = open(strPathFileSave,'w')

	xf.write('<ImpactPointSearchTask Series="IMPACT">\n')
	xf.write('\t<TaskID>{0}</TaskID>\n'.format(taskId))
	xf.write('\t<Label>{0}</Label>\n'.format(taskName))
	xf.write('\t<SearchLocation>\n')
	xf.write('\t\t<Location3D Series="CMASI">\n')
	xf.write('\t\t\t<Altitude>{0}</Altitude>\n'.format(point[2]))
	xf.write('\t\t\t<Latitude>{0}</Latitude>\n'.format(point[0]))
	xf.write('\t\t\t<Longitude>{0}</Longitude>\n'.format(point[1]))
	xf.write('\t\t</Location3D>\n')
	xf.write('\t</SearchLocation>\n')
	xf.write('\t<StandoffDistance>{0}</StandoffDistance>\n'.format(100))
	xf.write('\t<ViewAngleList>\n')
	xf.write('\t\t<Wedge Series="CMASI">\n')
	xf.write('\t\t\t<AzimuthCenterline>0.0</AzimuthCenterline>\n')
	xf.write('\t\t</Wedge>\n')
	xf.write('\t\t<Wedge Series="CMASI">\n')
	xf.write('\t\t\t<AzimuthCenterline>90.0</AzimuthCenterline>\n')
	xf.write('\t\t</Wedge>\n')
	xf.write('\t\t<Wedge Series="CMASI">\n')
	xf.write('\t\t\t<AzimuthCenterline>180.0</AzimuthCenterline>\n')
	xf.write('\t\t</Wedge>\n')
	xf.write('\t\t<Wedge Series="CMASI">\n')
	xf.write('\t\t\t<AzimuthCenterline>270.0</AzimuthCenterline>\n')
	xf.write('\t\t</Wedge>\n')
	xf.write('\t</ViewAngleList>\n')
	xf.write('\t<DesiredAction>\n')
	xf.write('\t\t<LoiterAction Series="CMASI">\n')
	xf.write('\t\t\t<Radius>{0}</Radius>\n'.format(400))
	xf.write('\t\t\t<Duration>{0}</Duration>\n'.format(-1))
	xf.write('\t\t\t<Location>\n')
	xf.write('\t\t\t\t<Location3D Series="CMASI">\n')
	xf.write('\t\t\t\t\t<Altitude>{0}</Altitude>\n'.format(point[2]))
	xf.write('\t\t\t\t\t<Latitude>{0}</Latitude>\n'.format(point[0]))
	xf.write('\t\t\t\t\t<Longitude>{0}</Longitude>\n'.format(point[1]))
	xf.write('\t\t\t\t</Location3D>\n')
	xf.write('\t\t\t</Location>\n')
	xf.write('\t\t</LoiterAction>\n')
	xf.write('\t</DesiredAction>\n')
	xf.write('\t<GroundSampleDistance>10000</GroundSampleDistance>\n')
	xf.write('</ImpactPointSearchTask>\n')

	xf.close()
	return fileName

def SavePointSearchTask(pathSave,taskId,taskName,point):
	fileName = '{0:3d}_PointSearchTask_{1}.xml'.format(taskId,taskName)
	strPathFileSave = pathSave + fileName
	xf = open(strPathFileSave,'w')

	xf.write('<PointSearchTask Series="CMASI">\n')
	xf.write('\t<TaskID>{0}</TaskID>\n'.format(taskId))
	xf.write('\t<Label>{0}</Label>\n'.format(taskName))
	xf.write('\t<StandoffDistance>{0}</StandoffDistance>\n'.format(100))

	xf.write('\t<SearchLocation>\n')
	xf.write('\t\t<Location3D Series="CMASI">\n')
	xf.write('\t\t\t<Altitude>{0}</Altitude>\n'.format(point[2]))
	xf.write('\t\t\t<Latitude>{0}</Latitude>\n'.format(point[0]))
	xf.write('\t\t\t<Longitude>{0}</Longitude>\n'.format(point[1]))
	xf.write('\t\t</Location3D>\n')
	xf.write('\t</SearchLocation>\n')
	xf.write('\t<ViewAngleList>\n')
	xf.write('\t\t<Wedge Series="CMASI">\n')
	xf.write('\t\t\t<AzimuthCenterline>0.0</AzimuthCenterline>\n')
	xf.write('\t\t</Wedge>\n')
	xf.write('\t\t<Wedge Series="CMASI">\n')
	xf.write('\t\t\t<AzimuthCenterline>90.0</AzimuthCenterline>\n')
	xf.write('\t\t</Wedge>\n')
	xf.write('\t\t<Wedge Series="CMASI">\n')
	xf.write('\t\t\t<AzimuthCenterline>180.0</AzimuthCenterline>\n')
	xf.write('\t\t</Wedge>\n')
	xf.write('\t\t<Wedge Series="CMASI">\n')
	xf.write('\t\t\t<AzimuthCenterline>270.0</AzimuthCenterline>\n')
	xf.write('\t\t</Wedge>\n')
	xf.write('\t</ViewAngleList>\n')
	# xf.write('\t<DesiredAction>\n')
	# xf.write('\t\t<LoiterAction Series="CMASI">\n')
	# xf.write('\t\t\t<Radius>{0}</Radius>\n'.format(400))
	# xf.write('\t\t\t<Duration>{0}</Duration>\n'.format(-1))
	# xf.write('\t\t\t<Location>\n')
	# xf.write('\t\t\t\t<Location3D Series="CMASI">\n')
	# xf.write('\t\t\t\t\t<Altitude>{0}</Altitude>\n'.format(point[2]))
	# xf.write('\t\t\t\t\t<Latitude>{0}</Latitude>\n'.format(point[0]))
	# xf.write('\t\t\t\t\t<Longitude>{0}</Longitude>\n'.format(point[1]))
	# xf.write('\t\t\t\t</Location3D>\n')
	# xf.write('\t\t\t</Location>\n')
	# xf.write('\t\t</LoiterAction>\n')
	# xf.write('\t</DesiredAction>\n')
	xf.write('\t<GroundSampleDistance>10000</GroundSampleDistance>\n')
	xf.write('</PointSearchTask>\n')

	xf.close()
	return fileName

def SaveDepot(pathSave,taskId,taskName,point):
	fileName = '{0:3d}_DepotTask_{1}.xml'.format(taskId,taskName)
	strPathFileSave = pathSave + fileName
	xf = open(strPathFileSave,'w')

	xf.write('<DepotTask Series="PISR">\n')
	xf.write('\t<TaskID>{0}</TaskID>\n'.format(taskId))
	xf.write('\t<Label>{0}</Label>\n'.format(taskName))
	xf.write('\t<DepotLocation>\n')
	xf.write('\t\t<Location3D Series="CMASI">\n')
	xf.write('\t\t\t<Altitude>{0}</Altitude>\n'.format(point[2]))
	xf.write('\t\t\t<Latitude>{0}</Latitude>\n'.format(point[0]))
	xf.write('\t\t\t<Longitude>{0}</Longitude>\n'.format(point[1]))
	xf.write('\t\t</Location3D>\n')
	xf.write('\t</DepotLocation>\n')
	xf.write('</DepotTask>\n')

	xf.close()
	return fileName

def SaveRoadAsLineSearches(pathSave,taskType,taskId,roadName,coordinatesPd):
	fileName = '{0:3d}_{1}_{2}.xml'.format(taskId,taskType,roadName)
	strPathFileSave = pathSave + fileName
	xf = open(strPathFileSave,'w')

	xf.write('<LineSearchTask Series="CMASI">\n')
	xf.write('\t<PointList>\n')
	for coordinate in coordinatesPd.itertuples():
		xf.write('\t\t<Location3D Series="CMASI"><Altitude>{0}</Altitude><Longitude>{1}</Longitude><Latitude>{2}</Latitude></Location3D>\n'
																.format(coordinate.altitude,coordinate.longitude,coordinate.latitude))
	xf.write('\t</PointList>\n')
	xf.write('\t<ViewAngleList></ViewAngleList>\n')
	xf.write('\t<UseInertialViewAngles>false</UseInertialViewAngles>\n')
	xf.write('\t<TaskID>{0}</TaskID>\n'.format(taskId))
	xf.write('\t<Label>{0}</Label>\n'.format(roadName))
	xf.write('\t<EligibleEntities></EligibleEntities>\n')

	xf.write('\t<ViewAngleList>\n')
	xf.write('\t\t<Wedge Series="CMASI">\n')
	xf.write('\t\t\t<AzimuthCenterline>35.0</AzimuthCenterline>\n')
	xf.write('\t\t\t<VerticalCenterline>60.0</VerticalCenterline>\n')
	xf.write('\t\t</Wedge>\n')
	xf.write('\t</ViewAngleList>\n')

	
	xf.write('\t<RevisitRate>0</RevisitRate>\n')
	xf.write('\t<Parameters></Parameters>\n')
	xf.write('\t<Priority>0</Priority>\n')
	xf.write('\t<Required>true</Required>\n')
	xf.write('\t<DesiredWavelengthBands><WavelengthBand>AllAny</WavelengthBand></DesiredWavelengthBands>\n')
	xf.write('\t<DwellTime>0</DwellTime>\n')
	xf.write('\t<GroundSampleDistance>1000</GroundSampleDistance>\n')
	xf.write('</LineSearchTask>\n')
	xf.close()
	return fileName

def SavePisr(pathSave,pisrTaskId,taskList,vehicleId,operatingRegionId):
	fileName = '{0:3d}_PISR_Task_FromKml_V{1}.xml'.format(pisrTaskId,vehicleId)
	strPathFileSave = pathSave + fileName
	xf = open(strPathFileSave,'w')

	xf.write('<PISR_Task Series="PISR">\n')
	xf.write('\t<TaskID>{0}</TaskID>\n'.format(pisrTaskId))
	xf.write('\t<Label>PISR_FromGoogleEarth</Label>\n')
	xf.write('\t<EligibleEntities><int64>{0}</int64></EligibleEntities>\n'.format(vehicleId))
	xf.write('\t<isListOrdered>false</isListOrdered>\n')
	xf.write('\t<OperatingRegion>{0}</OperatingRegion>\n'.format(operatingRegionId))
	xf.write('\t<!-- <AssignmentType>MWRRP</AssignmentType> -->\n')
	xf.write('\t<AssignmentType>LengthConstrainedMtsp</AssignmentType>\n')



	xf.write('\t<TaskList>\n')
	xf.write('\t\t<PISR_TaskList Series="PISR">\n')
	xf.write('\t\t\t<Beta_MWRRP>0.0</Beta_MWRRP>\n')
	xf.write('\t\t\t<TaskList>\n')
	for task in taskList:
		xf.write('\t\t\t\t<!-- {0} -->\n'.format(task[1]))
		xf.write('\t\t\t\t<PISR_SubTaskParameters Series="PISR"><TaskID>{0}</TaskID><MaximumDataLatency>1000000000</MaximumDataLatency><RevisitPeriod>1000000000</RevisitPeriod><RelativeTaskWeight>1.0</RelativeTaskWeight></PISR_SubTaskParameters>\n'.format(task[0]))
	xf.write('\t\t\t</TaskList>\n')
	xf.write('\t\t</PISR_TaskList>\n')
	xf.write('\t</TaskList>\n')
	xf.write('</PISR_Task>\n')
	xf.close()
	return fileName

def SaveAutomationRequest(pathSave,automationRequestId,taskId,taskName,vehicleId,operatingRegionId):
	fileName = '{0:3d}_AutomationRequest_{1}_V{2}.xml'.format(taskId,taskName,vehicleId)
	strPathFileSave = pathSave + fileName
	xf = open(strPathFileSave,'w')

	xf.write('<AutomationRequest Series="CMASI">\n')
	xf.write('\t<Label>PISR_FromGoogleEarth</Label>\n')
	xf.write('\t<EntityList><int64>{0}</int64></EntityList>\n'.format(vehicleId))
	xf.write('\t<TaskList><int64>{0}</int64></TaskList>\n'.format(taskId))
	xf.write('\t<OperatingRegion>{0}</OperatingRegion>\n'.format(operatingRegionId))
	xf.write('</AutomationRequest>\n')
	xf.close()
	return fileName

def SaveSectorSearch(pathSave,taskType,taskId,taskLabel,searchLongitude,searchLatitude,searchAltitude,extent,direction):
	fileName = '{0:3d}_{1}_{2}.xml'.format(taskId,taskType,taskLabel)
	strPathFileSave = pathSave + fileName
	xf = open(strPathFileSave,'w')

	xf.write('\t<PatternSearchTask Series="IMPACT">\n')
	xf.write('\t<TaskID>{0}</TaskID>\n'.format(taskId))
	xf.write('\t<Label>{0}</Label>\n'.format(taskLabel))
	xf.write('\t<EligibleEntities></EligibleEntities>\n')
	xf.write('\t<SearchLocation>\n')
	xf.write('\t\t<Location3D Series="CMASI"><Longitude>{0}</Longitude><Latitude>{1}</Latitude><Altitude>{2}</Altitude></Location3D>\n'
			  .format(searchLongitude,searchLatitude,searchAltitude))
	xf.write('\t</SearchLocation>\n')
   
	xf.write('\t<Pattern>Sector</Pattern>\n')
	xf.write('\t<Extent>{0}</Extent>\n'.format(extent))

	#<!-- from CMASI::Task: -->
	xf.write('\t<RevisitRate>0</RevisitRate>\n')
	xf.write('\t<Parameters></Parameters>\n')
	xf.write('\t<Priority>0</Priority>\n')
	xf.write('\t<Required>true</Required>\n')
	#<!-- from CMASI::SearchTask -->
	xf.write('\t<DesiredWavelengthBands><WavelengthBand>EO</WavelengthBand></DesiredWavelengthBands>\n')
	xf.write('\t<DwellTime>0</DwellTime>\n')
	xf.write('\t<GroundSampleDistance>5.0</GroundSampleDistance>\n')
	xf.write('\t</PatternSearchTask>\n')
	return fileName

def SaveAreaSearch(pathSave,taskType,taskId,taskLabel,coordinatesPd,direction):
	fileName = '{0:3d}_{1}_{2}.xml'.format(taskId,taskType,taskLabel)
	strPathFileSave = pathSave + fileName
	xf = open(strPathFileSave,'w')

	xf.write('\t<AreaSearchTask Series="CMASI">\n')
	xf.write('\t<TaskID>{0}</TaskID>\n'.format(taskId))
	xf.write('\t<Label>{0}</Label>\n'.format(taskLabel))
	xf.write('\t<EligibleEntities></EligibleEntities>\n')


	# xf.write('\t<ViewAngleList>\n')
	# xf.write('\t\t<Wedge Series="CMASI">\n')
	# xf.write('\t\t\t<AzimuthCenterline>0.0</AzimuthCenterline>\n')
	# xf.write('\t\t</Wedge>\n')
	# xf.write('\t\t<Wedge Series="CMASI">\n')
	# xf.write('\t\t\t<AzimuthCenterline>90.0</AzimuthCenterline>\n')
	# xf.write('\t\t</Wedge>\n')
	# xf.write('\t\t<Wedge Series="CMASI">\n')
	# xf.write('\t\t\t<AzimuthCenterline>180.0</AzimuthCenterline>\n')
	# xf.write('\t\t</Wedge>\n')
	# xf.write('\t\t<Wedge Series="CMASI">\n')
	# xf.write('\t\t\t<AzimuthCenterline>270.0</AzimuthCenterline>\n')
	# xf.write('\t\t</Wedge>\n')
	# xf.write('\t</ViewAngleList>\n')

	
	xf.write('\t<SearchArea>\n')
	xf.write('\t<Polygon Series="CMASI">\n')
	xf.write('\t<BoundaryPoints Series="CMASI">\n')
	for coordinate in coordinatesPd.itertuples():
				xf.write('\t\t<Location3D Series="CMASI"><Altitude>{0}</Altitude><Longitude>{1}</Longitude><Latitude>{2}</Latitude></Location3D>\n'
																																.format(coordinate.altitude,coordinate.longitude,coordinate.latitude))
	xf.write('\t</BoundaryPoints>\n')
	xf.write('\t</Polygon>\n')
	xf.write('\t</SearchArea>\n')

	xf.write('\t<UseInertialViewAngles>false</UseInertialViewAngles>\n')

	#<!-- from CMASI::Task: -->
	xf.write('\t<RevisitRate>0</RevisitRate>\n')
	xf.write('\t<Parameters></Parameters>\n')
	xf.write('\t<Priority>0</Priority>\n')
	xf.write('\t<Required>true</Required>\n')
	#<!-- from CMASI::SearchTask -->
	xf.write('\t<DesiredWavelengthBands><WavelengthBand>EO</WavelengthBand></DesiredWavelengthBands>\n')
	xf.write('\t<DwellTime>0</DwellTime>\n')
	xf.write('\t<GroundSampleDistance>5.0</GroundSampleDistance>\n')
	xf.write('\t</AreaSearchTask>\n')
	return fileName

def SaveKeepInOut(pathSave,zoneType,zoneId,zoneName,coordinatesPd):
	fileName = '{0:3d}_{1}_{2}.xml'.format(zoneId,zoneType,zoneName)
	strPathFileSave = '{0}{1}'.format(pathSave,fileName)
	xf = open(strPathFileSave,'w')

	xf.write('<{0} Series="CMASI">\n'.format(zoneType))
	xf.write('\t<ZoneID>{0}</ZoneID>\n'.format(zoneId))
	xf.write('\t<Label>{0}</Label>\n'.format(zoneName))
	if zoneType == 'KeepOutZone':
		xf.write('\t<ZoneType>Physical</ZoneType>\n')
	xf.write('\t<MinAltitude>-3.40282346638529e+38</MinAltitude>\n')
	xf.write('\t<MaxAltitude>3.40282346638529e+38</MaxAltitude>\n')
	xf.write('\t<AffectedAircraft></AffectedAircraft>\n')
	xf.write('\t<StartTime>0</StartTime>\n')
	xf.write('\t<EndTime>0</EndTime>\n')
	xf.write('\t<Padding>0.0</Padding>\n')
	xf.write('\t<Boundary>\n')
	xf.write('\t<Polygon Series="CMASI">\n')
	xf.write('\t<BoundaryPoints>\n')
	for coordinate in coordinatesPd.itertuples():
		xf.write('\t\t<Location3D Series="CMASI"><Altitude>{0}</Altitude><Longitude>{1}</Longitude><Latitude>{2}</Latitude></Location3D>\n'
																.format(coordinate.altitude,coordinate.longitude,coordinate.latitude))
	xf.write('\t</BoundaryPoints>\n')
	xf.write('\t</Polygon>\n')
	xf.write('\t</Boundary>\n')
	xf.write('</{0}>\n'.format(zoneType))
	xf.close()
	return fileName

def SaveOperatingRegion(pathSave,taskId,keepInZoneIds,keepOutZoneIds):
	fileName = '{0}_OperatingRegion_All.xml'.format(taskId)
	strPathFileSave = '{0}{1}'.format(pathSave,fileName)
	xf = open(strPathFileSave,'w')

	xf.write('<OperatingRegion Series="CMASI">\n')
	xf.write('  <ID>{0}</ID>\n'.format(taskId))
	xf.write('	 <KeepInAreas>\n')
	for id in keepInZoneIds:
		xf.write('	    <!-- {0} -->\n'.format(id[1]))
		xf.write('	    <uint32>{0}</uint32>\n'.format(id[0]))
	xf.write('	 </KeepInAreas>\n')
	xf.write('	 <KeepOutAreas>\n')
	for id in keepOutZoneIds:
		xf.write('	    <!-- {0} -->\n'.format(id[1]))
		xf.write('	    <uint32>{0}</uint32>\n'.format(id[0]))
	xf.write('	 </KeepOutAreas>\n')
	xf.write('</OperatingRegion>\n')
	xf.close()
	return fileName

# 
def ProcessKml(filename,pathSave,filePccBoundries,taskId,boundaryId):

	tree = etree.parse(filename)
	root = tree.getroot()

	keepInZoneIds = []
	keepOutZoneIds = []
	taskList = []
	taskFileNames = []
	for element in root.iter("{http://www.opengis.net/kml/2.2}Placemark"):
		# print('element[{0}]'.format(element.tag))
		visibilityElement = element.find("{http://www.opengis.net/kml/2.2}visibility")
		isVisible = True
		if visibilityElement != None:
			if '0' in visibilityElement.text:
				isVisible = False
		if isVisible:
			type = element.find("{http://www.opengis.net/kml/2.2}name")
			elementLabel = type.text.replace(" ", "_")
			if type != None:
				# print('elementLabel[{0}]'.format(elementLabel))
				if ('ROAD_' in elementLabel) or ('LINE_' in elementLabel):
					print(elementLabel)
					taskType = 'LineSearch'
					lineString = element.find('{http://www.opengis.net/kml/2.2}LineString')
					if lineString != None:
						coordinates = lineString.find('{http://www.opengis.net/kml/2.2}coordinates')
						if coordinates != None:
							coordinateArray=[]
							stringTemp = coordinates.text
							listCoords = stringTemp.split(' ')
							for coord in listCoords:
								coord = coord.lstrip()
								if len(coord) >= 3:
									longitude,latitude,altitude = coord.split(',',3)
									coordinateArray.append([latitude,longitude,altitude])
								coordinatesPd = pd.DataFrame(data = coordinateArray,columns=['latitude','longitude','altitude'])
							taskFileNames.append(SaveRoadAsLineSearches(pathSave,taskType,taskId,elementLabel,coordinatesPd))
							SaveBoundaryToPcc(filePccBoundries,taskId,elementLabel,taskType,coordinatesPd)
							taskList.append([taskId,elementLabel])
				elif  'sector_'  in elementLabel:
					print(elementLabel)
					taskId = 0
					taskIdRE = re.search(r'(_id\d{4})',elementLabel)
					taskIdString = taskIdRE.group(0).replace('_id','')
					taskId = long(taskIdString)
					taskType = 'SectorSearch'
					extent = 0
					extentRE = re.search(r'(_r\d{4})',elementLabel)
					extentString = extentRE.group(0).replace('_r','')
					extent = long(extentString)
					direction = 0
					directionRE = re.search(r'(_dir\d{3})',elementLabel)
					directionString = directionRE.group(0).replace('_dir','')
					direction = long(directionString)
					point = element.find('{http://www.opengis.net/kml/2.2}Point')
					if point != None:
						coordinates = point.find('{http://www.opengis.net/kml/2.2}coordinates')
						if coordinates != None:
							coordinateArray=[]
							stringTemp = coordinates.text
							listCoords = stringTemp.split(' ')
							for coord in listCoords:
								coord = coord.lstrip()
								if len(coord) >= 3:
									longitude,latitude,altitude = coord.split(',',3)
									taskFileNames.append(SaveSectorSearch(pathSave,taskType,taskId,elementLabel,longitude,latitude,altitude,extent,direction))
									SaveBoundaryToPcc(filePccBoundries,taskId,elementLabel,taskType,coordinatesPd)
									taskList.append([taskId,elementLabel])
								break

				elif  'POINT_' in elementLabel:
					print(elementLabel)
					point = element.find('{http://www.opengis.net/kml/2.2}Point')
					if point != None:
						coordinates = point.find('{http://www.opengis.net/kml/2.2}coordinates')
						if coordinates != None:
							coordinateArray=[]
							stringTemp = coordinates.text
							listCoords = stringTemp.split(' ')
							longitude_f = 0.0
							latitude_f = 0.0
							for coord in listCoords:
								coord = coord.lstrip()

								if len(coord) >= 3:
									longitude,latitude,altitude = coord.split(',',3)
									longitude_f = float(longitude)
									latitude_f = float(latitude)
									coordinateArray.append([latitude,longitude_f,altitude])
							newLatitude = latitude_f + 0.0001
							newLongitude = longitude_f + 0.0001
							coordinateArray.append([newLatitude,newLongitude,altitude])
							newLongitude = longitude_f - 0.0001
							coordinateArray.append([newLatitude,newLongitude,altitude])
							newLatitude = latitude_f - 0.0001
							coordinateArray.append([newLatitude,newLongitude,altitude])
							coordinatesPd = pd.DataFrame(data = coordinateArray,columns=['latitude','longitude','altitude'])

							SaveBoundaryToPcc(filePccBoundries,taskId,elementLabel,taskType,coordinatesPd)

							taskFileNames.append(SavePointSearchTask(pathSave,taskId,elementLabel,[latitude,longitude,altitude]))
							taskList.append([taskId,elementLabel])
				elif  'DEPOT_' in elementLabel:
					print(elementLabel)
					depotElement = element.find('{http://www.opengis.net/kml/2.2}Point')
					if depotElement != None:
						coordinates = depotElement.find('{http://www.opengis.net/kml/2.2}coordinates')
						if coordinates != None:
							coordinateArray=[]
							stringTemp = coordinates.text
							listCoords = stringTemp.split(' ')
							longitude_f = 0.0
							latitude_f = 0.0
							for coord in listCoords:
								coord = coord.lstrip()

								if len(coord) >= 3:
									longitude,latitude,altitude = coord.split(',',3)
									longitude_f = float(longitude)
									latitude_f = float(latitude)
									coordinateArray.append([latitude,longitude_f,altitude])
							newLatitude = latitude_f + 0.0001
							newLongitude = longitude_f + 0.0001
							coordinateArray.append([newLatitude,newLongitude,altitude])
							newLongitude = longitude_f - 0.0001
							coordinateArray.append([newLatitude,newLongitude,altitude])
							newLatitude = latitude_f - 0.0001
							coordinateArray.append([newLatitude,newLongitude,altitude])
							coordinatesPd = pd.DataFrame(data = coordinateArray,columns=['latitude','longitude','altitude'])

							SaveBoundaryToPcc(filePccBoundries,taskId,elementLabel,taskType,coordinatesPd)

							taskFileNames.append(SaveDepot(pathSave,taskId,elementLabel,[latitude,longitude,altitude]))
							taskList.append([taskId,elementLabel])
				elif  'ACP_' in elementLabel:
					print(elementLabel)
					point = element.find('{http://www.opengis.net/kml/2.2}Point')
					if point != None:
						coordinates = point.find('{http://www.opengis.net/kml/2.2}coordinates')
						if coordinates != None:
							coordinateArray=[]
							stringTemp = coordinates.text
							listCoords = stringTemp.split(' ')
							for coord in listCoords:
								coord = coord.lstrip()
								if len(coord) >= 3:
									longitude,latitude,altitude = coord.split(',',3)
									coordinateArray.append([latitude,longitude,altitude])
								coordinatesPd = pd.DataFrame(data = coordinateArray,columns=['latitude','longitude','altitude'])
							taskFileNames.append(SaveProceedToPointAndHoldTask(pathSave,taskId,elementLabel,[latitude,longitude,altitude]))
							taskList.append([taskId,elementLabel])
				elif  'spiral_'  in elementLabel:
					print(elementLabel)
					point = element.find('{http://www.opengis.net/kml/2.2}Point')
					if point != None:
						coordinates = point.find('{http://www.opengis.net/kml/2.2}coordinates')
						if coordinates != None:
							coordinateArray=[]
							stringTemp = coordinates.text
							listCoords = stringTemp.split(' ')
							for coord in listCoords:
								coord = coord.lstrip()
								if len(coord) >= 3:
									longitude,latitude,altitude = coord.split(',',3)
									coordinateArray.append([latitude,longitude,altitude])
								coordinatesPd = pd.DataFrame(data = coordinateArray,columns=['latitude','longitude','altitude'])
							taskList.append([taskId,elementLabel])
				elif  ('area_' in elementLabel) or ('AREA_' in elementLabel):
					print(elementLabel)
					taskType = 'AreaSearch'
					direction = 0
					# directionRE = re.search(r'(_dir\d{3})',elementLabel)
					# directionString = directionRE.group(0).replace('_dir','')
					# direction = long(directionString)
					polygon = element.find('{http://www.opengis.net/kml/2.2}Polygon')
					if polygon != None:
						outerBoundaryIs = polygon.find('{http://www.opengis.net/kml/2.2}outerBoundaryIs')
						if outerBoundaryIs != None:
							linearRing = outerBoundaryIs.find('{http://www.opengis.net/kml/2.2}LinearRing')
							if linearRing != None:
								coordinates = linearRing.find('{http://www.opengis.net/kml/2.2}coordinates')
								if coordinates != None:
									coordinateArray=[]
									stringTemp = coordinates.text
									listCoords = stringTemp.split(' ')
									for coord in listCoords:
										coord = coord.lstrip()
										if len(coord) >= 3:
											longitude,latitude,altitude = coord.split(',',3)
											coordinateArray.append([latitude,longitude,altitude])
										coordinatesPd = pd.DataFrame(data = coordinateArray,columns=['latitude','longitude','altitude'])
							taskFileNames.append(SaveAreaSearch(pathSave,taskType,taskId,elementLabel,coordinatesPd,direction))
							SaveBoundaryToPcc(filePccBoundries,taskId,elementLabel,taskType,coordinatesPd)
							taskList.append([taskId,elementLabel])
				elif  ('TERRAIN_' in elementLabel) or ('KEEPOUT_' in elementLabel):
					print(elementLabel)
					zoneType = 'KeepOutZone'
					polygon = element.find('{http://www.opengis.net/kml/2.2}Polygon')
					if polygon != None:
						outerBoundaryIs = polygon.find('{http://www.opengis.net/kml/2.2}outerBoundaryIs')
						if outerBoundaryIs != None:
							linearRing = outerBoundaryIs.find('{http://www.opengis.net/kml/2.2}LinearRing')
							if linearRing != None:
								coordinates = linearRing.find('{http://www.opengis.net/kml/2.2}coordinates')
								if coordinates != None:
									coordinateArray=[]
									stringTemp = coordinates.text
									listCoords = stringTemp.split(' ')
									for coord in listCoords:
										coord = coord.lstrip()
										if len(coord) >= 3:
											longitude,latitude,altitude = coord.split(',',3)
											coordinateArray.append([latitude,longitude,altitude])
										coordinatesPd = pd.DataFrame(data = coordinateArray,columns=['latitude','longitude','altitude'])
									taskFileNames.append(SaveKeepInOut(pathSave,zoneType,taskId,elementLabel,coordinatesPd))
									SaveBoundaryToPcc(filePccBoundries,taskId,elementLabel,zoneType,coordinatesPd)
									keepOutZoneIds.append([taskId,elementLabel])
				elif  ('SECTOR_' in elementLabel) or ('AIR_CORRIDOR_' in elementLabel) or ('LRS_ROZ_' in elementLabel) or ('ICE-T ' in elementLabel) or ('KEEPIN_' in elementLabel):
					print(elementLabel)
					zoneType = 'KeepInZone'
					polygon = element.find('{http://www.opengis.net/kml/2.2}Polygon')
					if polygon != None:
						outerBoundaryIs = polygon.find('{http://www.opengis.net/kml/2.2}outerBoundaryIs')
						if outerBoundaryIs != None:
							linearRing = outerBoundaryIs.find('{http://www.opengis.net/kml/2.2}LinearRing')
							if linearRing != None:
								coordinates = linearRing.find('{http://www.opengis.net/kml/2.2}coordinates')
								if coordinates != None:
									coordinateArray=[]
									stringTemp = coordinates.text
									listCoords = stringTemp.split(' ')
									for coord in listCoords:
										coord = coord.lstrip()
										if len(coord) >= 3:
											longitude,latitude,altitude = coord.split(',',3)
											coordinateArray.append([latitude,longitude,altitude])
										coordinatesPd = pd.DataFrame(data = coordinateArray,columns=['latitude','longitude','altitude'])
									taskFileNames.append(SaveKeepInOut(pathSave,zoneType,taskId,elementLabel,coordinatesPd))
									taskType = zoneType
									SaveBoundaryToPcc(filePccBoundries,taskId,elementLabel,zoneType,coordinatesPd)
									keepInZoneIds.append([taskId,elementLabel])
			taskId = taskId + 1

	operatingRegionId = taskId
	taskFileNames.append(SaveOperatingRegion(pathSave,operatingRegionId,keepInZoneIds,keepOutZoneIds))
	taskId = taskId + 1

	return taskFileNames, taskList, taskId, operatingRegionId

def main():
	pathSave = 'tasks/'
	if not os.path.exists(pathSave):
		os.makedirs(pathSave)

	pathSavePcc = 'PccFiles_Tasks/'
	if not os.path.exists(pathSavePcc):
		os.makedirs(pathSavePcc)
	fileNamePccBoundaries = '{0}Boundaries.tasks.xml'.format(pathSavePcc)
	filePccBoundries = open(fileNamePccBoundaries,'w')
	filePccBoundries.write('<!DOCTYPE AirspaceBoundaries>\n<AirspaceBoundaries>\n')

	taskId = 1000
	boundaryId = 5000
	taskFileNames = []
	taskList = []

	taskIdFinal = taskId
	operatingRegionId = 1000
	for kmlFile in glob.glob('*.kml'):
		print 'loading [' + kmlFile + ']'
		taskFileNamesReturn,taskListReturn, taskIdFinal,operatingRegionId = ProcessKml(kmlFile,pathSave,filePccBoundries,taskIdFinal,boundaryId)
		taskFileNames.extend(taskFileNamesReturn)
		taskList.extend(taskListReturn)

	filePccBoundries.write('</AirspaceBoundaries>\n')
	filePccBoundries.close()

	vehicleIds = [400,500]
	for vehicleId in vehicleIds:
		taskFileNames.extend([SavePisr(pathSave,taskIdFinal,taskList,vehicleId,operatingRegionId)])
		taskIdFinal = taskIdFinal + 1		

	saveSendMessagesTestServiceFile = pathSave + 'SendMessagesTestServiceFile.xml'
	xf = open(saveSendMessagesTestServiceFile,'w')
	for taskFileName in taskFileNames:
		xf.write('\t\t<Message MessageFileName="{0}{1}" SendTime_ms="1000"/>\n'.format(pathSave,taskFileName))
	xf.close()	

	pathSaveAutomationRequests = 'AutomationRequests/'
	if not os.path.exists(pathSaveAutomationRequests):
		os.makedirs(pathSaveAutomationRequests)

	for vehicleId in vehicleIds:
		pathSaveAutomationRequestVehicle = '{0}V{1}/'.format(pathSaveAutomationRequests,vehicleId)
		if not os.path.exists(pathSaveAutomationRequestVehicle):
			os.makedirs(pathSaveAutomationRequestVehicle)
		for task in taskList:
			SaveAutomationRequest(pathSaveAutomationRequestVehicle,taskIdFinal,task[0],task[1],vehicleId,operatingRegionId)			
			taskIdFinal = taskIdFinal + 1		



if __name__ == '__main__':
	main()
