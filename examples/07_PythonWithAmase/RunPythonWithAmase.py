import zmq, sys, time, copy, re
import xml.dom.minidom
from xml.dom.minidom import parse, parseString

# Include LMCP Python files
sys.path.append('../../src/LMCP/py')
from lmcp import LMCPFactory
from afrl.cmasi import *


def create_and_run_amase_scenario():
    ###################################################################################################################
    # Prepare a ZeroMQ context and socket, then connect to 5555. This is the port AMASE uses by convention.
    # The actual port is set by an XML element in the file Plugins.xml, whose location is specified with the AMASE
    # option --config <config_directory> when starting up AMASE. This XML element has the form:
    # <Plugin Class="avtas.amase.network.TcpServer">
    #    <TCPServer Port="5555"/>
    # </Plugin>
    # -----------------------------------------------------------------------------------------------------------------

    context = zmq.Context()
    socket = context.socket(zmq.STREAM)
    socket.connect("tcp://127.0.0.1:5555")
    # Store the client ID for this socket
    client_id, message = socket.recv_multipart()

    ###################################################################################################################
    # Initialize an LMCPFactory for creating LMCP messages
    # -----------------------------------------------------------------------------------------------------------------

    factory = LMCPFactory.LMCPFactory()

    ###################################################################################################################
    # Create an AirVehicleConfiguration message object from 'scratch'. This requires several sub-message objects:
    #
    # FlightProfile       -- at least one FlightProfile that describes the basic dynamics of the aircraft
    # GimbalConfiguration -- information about the aircraft's gimbal (can be more than one)
    # CameraConfiguration -- information about the aircraft's camera (can be more than one per gimbal)
    #
    # LMCP should default to sane values for unset parameters.
    # -----------------------------------------------------------------------------------------------------------------

    fp_obj = factory.createObjectByName("CMASI", "FlightProfile")
    fp_obj.set_Name("Cruise")
    fp_obj.set_Airspeed(27.5)
    fp_obj.set_PitchAngle(0.0)
    fp_obj.set_VerticalSpeed(0.0)
    fp_obj.set_MaxBankAngle(30.0)
    fp_obj.set_EnergyRate(0.02)

    cc_obj = factory.createObjectByName("CMASI", "CameraConfiguration")
    cc_obj.set_SupportedWavelengthBand(WavelengthBand.WavelengthBand.AllAny)
    cc_obj.set_FieldOfViewMode(FOVOperationMode.FOVOperationMode.Discrete)
    cc_obj.set_MinHorizontalFieldOfView(0.11)
    cc_obj.set_MaxHorizontalFieldOfView(45.0)
    cc_obj.DiscreteHorizontalFieldOfViewList = [45.0, 22.0, 7.6, 3.7, 0.63, 0.11]
    cc_obj.set_VideoStreamHorizontalResolution(1024)
    cc_obj.set_VideoStreamVerticalResolution(768)
    # Camera PayloadIDs do not have to be unique across different vehicles, since AMASE and UxAS reason about payloads
    # on a per vehicle basis. However, it is good practice to give each payload a unique ID, even across vehicles.
    cc_obj.set_PayloadID(10001)

    gc_obj = factory.createObjectByName("CMASI", "GimbalConfiguration")
    gc_obj.SupportedPointingModes = [GimbalPointingMode.GimbalPointingMode.AirVehicleRelativeAngle]
    gc_obj.set_MinAzimuth(-180.0)
    gc_obj.set_MaxAzimuth(180.0)
    gc_obj.set_MinElevation(-180.0)
    gc_obj.set_MaxElevation(180.0)
    gc_obj.set_MinRotation(-180.0)
    gc_obj.set_MaxRotation(180.0)
    gc_obj.set_IsAzimuthClamped(False)
    gc_obj.set_IsElevationClamped(False)
    gc_obj.set_IsRotationClamped(False)
    gc_obj.set_MaxAzimuthSlewRate(30.0)
    gc_obj.set_MaxElevationSlewRate(30.0)
    gc_obj.set_MaxRotationRate(30.0)
    # Gimbal PayloadIDs do not have to be unique across different vehicles, since AMASE and UxAS reason about payloads
    # on a per vehicle basis. However, it is good practice to give each payload a unique ID, even across vehicles.
    gc_obj.set_PayloadID(1001)
    gc_obj.ContainedPayloadList = [10001]

    avc_obj = factory.createObjectByName("CMASI", "AirVehicleConfiguration")
    avc_obj.set_ID(1)
    avc_obj.set_Label("UAV1")
    avc_obj.set_MinimumSpeed(15.0)
    avc_obj.set_MaximumSpeed(35.0)
    avc_obj.set_NominalSpeed(27.5)
    avc_obj.set_MinimumAltitude(0.0)
    avc_obj.set_MaximumAltitude(1000000.0)
    avc_obj.set_NominalAltitude(700.0)
    avc_obj.set_NominalFlightProfile(fp_obj)
    # Lists do not have 'set' methods; they are accessed directly. This is consistent in concept with LMCP in C++,
    # where the 'get' method returns a reference that is used to directly set values.
    avc_obj.PayloadConfigurationList = [cc_obj, gc_obj]

    send_to_amase(avc_obj, socket, client_id)

    ###################################################################################################################
    # Create an AirVehicleState message object from 'scratch' for the AirVehicleConfiguration above.
    # This requires several sub-message objects:
    #
    # Location3D -- the initial location of the vehicle
    # GimbalState -- one for each GimbalConfiguration
    # CameraState -- one for each CameraConfiguration
    #
    # LMCP should default to sane values for unset parameters.
    # -----------------------------------------------------------------------------------------------------------------

    loc_obj = factory.createObjectByName("CMASI", "Location3D")
    loc_obj.set_Altitude(700.0)
    loc_obj.set_Latitude(1.5152)
    loc_obj.set_Longitude(-132.5299)

    cs_obj = factory.createObjectByName("CMASI", "CameraState")
    cs_obj.set_HorizontalFieldOfView(20.0)
    cs_obj.set_PayloadID(10001)

    gs_obj = factory.createObjectByName("CMASI", "GimbalState")
    gs_obj.set_PointingMode(GimbalPointingMode.GimbalPointingMode.AirVehicleRelativeAngle)
    gs_obj.set_Azimuth(0.0)
    gs_obj.set_Elevation(-45.0)
    gs_obj.set_Rotation(0.0)
    gs_obj.set_PayloadID(1001)

    avs_obj = factory.createObjectByName("CMASI", "AirVehicleState")
    avs_obj.set_ID(1)
    avs_obj.set_Airspeed(27.5)
    avs_obj.set_EnergyAvailable(100.0)
    avs_obj.set_Location(loc_obj)
    avs_obj.PayloadStateList = [cs_obj, gs_obj]

    send_to_amase(avs_obj, socket, client_id)

    ###################################################################################################################
    # Create a second air vehicle by copying and modifying the previous AirVehicleConfiguration and AirVehicleState.
    # Add some additional FlightProfiles for ascending, descending, dashing, and loitering.
    # -----------------------------------------------------------------------------------------------------------------

    avc2_obj = copy.deepcopy(avc_obj)
    # Each air vehicle must have a unique ID, so change it here. Label is simply used for display purposes in AMASE.
    avc2_obj.set_ID(2)
    avc2_obj.set_Label("UAV2")
    # Modify speeds and NominalFlightProfile
    avc2_obj.set_MinimumSpeed(10.0)
    avc2_obj.set_NominalSpeed(30.0)
    avc2_obj.set_MaximumSpeed(40.0)
    avc2_obj.set_NominalAltitude(500.0)
    avc2_obj.get_NominalFlightProfile().set_Airspeed(30.0)
    avc2_obj.get_NominalFlightProfile().set_EnergyRate(0.03)
    # Base the CameraConfiguration of UAV2's camera on that of UAV1, but change the WavelengthBand, FieldOfViewMode,
    # MinHorizontalFieldOfView, MaxHorizontalFieldOfView, and PayloadID.
    # Camera PayloadIDs do not have to be unique across vehicles, since AMASE and UxAS reason about payloads on a per
    # vehicle basis. However, it is good practice to give each payload a unique ID, even across vehicles.
    avc2_obj.PayloadConfigurationList[0].set_SupportedWavelengthBand(WavelengthBand.WavelengthBand.EO)
    avc2_obj.get_PayloadConfigurationList()[0].set_FieldOfViewMode(FOVOperationMode.FOVOperationMode.Continuous)
    avc2_obj.get_PayloadConfigurationList()[0].DiscreteHorizontalFieldOfViewList = []
    avc2_obj.get_PayloadConfigurationList()[0].set_MinHorizontalFieldOfView(5.0)
    avc2_obj.get_PayloadConfigurationList()[0].set_MaxHorizontalFieldOfView(50.0)
    avc2_obj.get_PayloadConfigurationList()[0].set_PayloadID(10002)
    # Base the GimbalConfiguration of UAV2's gimbal on that of UAV1, but change the slew rates, the PayloadID, and set
    # the ContainedPayloadList to refer to the PayloadID of the modified camera.
    # Gimbal PayloadIDs do not have to be unique across vehicles, since AMASE and UxAS reason about payloads on a per
    # vehicle basis. However, it is good practice to give each payload a unique ID, even across vehicles.
    avc2_obj.get_PayloadConfigurationList()[1].set_MaxAzimuthSlewRate(45.0)
    avc2_obj.get_PayloadConfigurationList()[1].set_MaxElevationSlewRate(45.0)
    avc2_obj.get_PayloadConfigurationList()[1].set_MaxRotationRate(45.0)
    avc2_obj.get_PayloadConfigurationList()[1].set_PayloadID(1002)
    avc2_obj.get_PayloadConfigurationList()[1].ContainedPayloadList = [10002]
    # Add additional FlightProfiles for climbing, descending, loitering, and dashing
    fp_climb_obj = factory.createObjectByName("CMASI", "FlightProfile")
    fp_climb_obj.set_Name("Climb")
    fp_climb_obj.set_Airspeed(25.0)
    fp_climb_obj.set_PitchAngle(10.0)
    fp_climb_obj.set_VerticalSpeed(5.0)
    fp_climb_obj.set_MaxBankAngle(30.0)
    fp_climb_obj.set_EnergyRate(0.1)
    fp_descent_obj = factory.createObjectByName("CMASI", "FlightProfile")
    fp_descent_obj.set_Name("Descent")
    fp_descent_obj.set_Airspeed(25.0)
    fp_descent_obj.set_PitchAngle(-5.0)
    fp_descent_obj.set_VerticalSpeed(-5.0)
    fp_descent_obj.set_MaxBankAngle(30.0)
    fp_descent_obj.set_EnergyRate(0.005)
    fp_loiter_obj = factory.createObjectByName("CMASI", "FlightProfile")
    fp_loiter_obj.set_Name("Loiter")
    fp_loiter_obj.set_Airspeed(20.0)
    fp_loiter_obj.set_PitchAngle(5.0)
    fp_loiter_obj.set_VerticalSpeed(0.0)
    fp_loiter_obj.set_MaxBankAngle(30.0)
    fp_loiter_obj.set_EnergyRate(0.025)
    fp_dash_obj = factory.createObjectByName("CMASI", "FlightProfile")
    fp_dash_obj.set_Name("Dash")
    fp_dash_obj.set_Airspeed(35.0)
    fp_dash_obj.set_PitchAngle(-2.0)
    fp_dash_obj.set_VerticalSpeed(0.0)
    fp_dash_obj.set_MaxBankAngle(30.0)
    fp_dash_obj.set_EnergyRate(0.1)
    avc2_obj.AlternateFlightProfiles = [fp_climb_obj, fp_descent_obj, fp_loiter_obj, fp_dash_obj]

    send_to_amase(avc2_obj, socket, client_id)

    avs2_obj = copy.deepcopy(avs_obj)
    avs2_obj.set_ID(2)
    avs2_obj.set_Airspeed(30.0)
    avs2_obj.get_Location().set_Altitude(500.0)
    avs2_obj.get_Location().set_Longitude(-132.5405)
    avs2_obj.get_PayloadStateList()[0].set_HorizontalFieldOfView(25.0)
    avs2_obj.get_PayloadStateList()[0].set_PayloadID(10002)
    avs2_obj.get_PayloadStateList()[1].set_Azimuth(-70.0)
    avs2_obj.get_PayloadStateList()[1].set_Elevation(-70.0)
    avs2_obj.get_PayloadStateList()[1].set_PayloadID(1002)

    send_to_amase(avs2_obj, socket, client_id)

    ###################################################################################################################
    # Create a third air vehicle by loading base configuration and state information from XML files.
    # Modify IDs and PayloadIDs to be unique.
    # -----------------------------------------------------------------------------------------------------------------

    cc3_lmcp_dom = parse("messageLibrary/CameraConfiguration_WavelengthAnyAll_FovDiscrete_PayloadID-10001.xml")
    obj_list = factory.unpackFromXMLNode(cc3_lmcp_dom)
    cc3_obj = obj_list[0]
    cc3_obj.set_PayloadID(10003)
    gc3_lmcp_dom = parse("messageLibrary/GimbalConfiguration_ClampedFalse_PayloadID-1001.xml")
    obj_list = factory.unpackFromXMLNode(gc3_lmcp_dom)
    gc3_obj = obj_list[0]
    gc3_obj.set_PayloadID(1003)
    gc3_obj.ContainedPayloadList = [10003]
    avc3_lmcp_dom = parse("messageLibrary/AirVehicleConfiguration_FlightProfileAll_LoiterAll_ID-1.xml")
    obj_list = factory.unpackFromXMLNode(avc3_lmcp_dom)
    avc3_obj = obj_list[0]
    avc3_obj.set_ID(3)
    avc3_obj.set_Label("UAV3")
    avc3_obj.PayloadConfigurationList = [cc3_obj, gc3_obj]

    send_to_amase(avc3_obj, socket, client_id)

    cs3_lmcp_dom = parse("messageLibrary/CameraState_PayloadID-10001.xml")
    obj_list = factory.unpackFromXMLNode(cs3_lmcp_dom)
    cs3_obj = obj_list[0]
    cs3_obj.set_PayloadID(10003)
    gs3_lmcp_dom = parse("messageLibrary/GimbalState_PayloadID-1001.xml")
    obj_list = factory.unpackFromXMLNode(gs3_lmcp_dom)
    gs3_obj = obj_list[0]
    gs3_obj.set_PayloadID(1003)
    avs3_lmcp_dom = parse("messageLibrary/AirVehicleState_FlightProfileAll_LoiterAll_ID-1.xml")
    obj_list = factory.unpackFromXMLNode(avs3_lmcp_dom)
    avs3_obj = obj_list[0]
    avs3_obj.set_ID(3)
    longitude = (avs_obj.get_Location().get_Longitude() + avs2_obj.get_Location().get_Longitude()) / 2.0
    latitude = avs_obj.get_Location().get_Latitude() - 0.01
    avs3_obj.get_Location().set_Longitude(longitude)
    avs3_obj.get_Location().set_Latitude(latitude)
    avs3_obj.PayloadStateList = [cs3_obj, gs3_obj]

    send_to_amase(avs3_obj, socket, client_id)

    ###################################################################################################################
    # Construct commands for the vehicles and send them.
    # -----------------------------------------------------------------------------------------------------------------

    # Command air vehicle 1 to visit two different waypoints repeatedly, then 1 second later, command the gimbal to
    # stare at a particular point from that time onward
    wp101_obj = factory.createObjectByName("CMASI", "Waypoint")
    wp101_obj.set_Number(101)
    wp101_obj.set_NextWaypoint(102)
    wp101_obj.set_Speed(25.0)
    wp101_obj.set_Latitude(1.5109)
    wp101_obj.set_Longitude(-132.5383)
    wp101_obj.set_Altitude(700.0)
    wp102_obj = factory.createObjectByName("CMASI", "Waypoint")
    wp102_obj.set_Number(102)
    wp102_obj.set_NextWaypoint(101)
    wp102_obj.set_Speed(25.0)
    wp102_obj.set_Latitude(1.5169)
    wp102_obj.set_Longitude(-132.5455)
    wp102_obj.set_Altitude(700.0)
    mc11_obj = factory.createObjectByName("CMASI", "MissionCommand")
    mc11_obj.set_FirstWaypoint(101)
    mc11_obj.set_CommandID(11)
    mc11_obj.set_VehicleID(1)
    mc11_obj.WaypointList = [wp101_obj, wp102_obj]

    gsa_obj = factory.createObjectByName("CMASI", "GimbalStareAction")
    locgsa_obj = factory.createObjectByName("CMASI", "Location3D")
    locgsa_obj.set_Latitude(1.5147)
    locgsa_obj.set_Longitude(-132.5405)
    gsa_obj.set_Starepoint(locgsa_obj)
    gsa_obj.set_PayloadID(1001)
    vac12_obj = factory.createObjectByName("CMASI", "VehicleActionCommand")
    vac12_obj.set_CommandID(12)
    vac12_obj.set_VehicleID(1)
    vac12_obj.VehicleActionList = [gsa_obj]

    time.sleep(2.0)
    send_to_amase(mc11_obj, socket, client_id)
    time.sleep(1.0)
    send_to_amase(vac12_obj, socket, client_id)

    # Command air vehicle 2 to follow a MissionCommand consisting of ordered waypoints that form a closed polygon.
    wp201_obj = factory.createObjectByName("CMASI", "Waypoint")
    wp201_obj.set_Number(201)
    wp201_obj.set_NextWaypoint(202)
    wp201_obj.set_Speed(20.0)
    wp201_obj.set_Latitude(1.5217)
    wp201_obj.set_Longitude(-132.5349)
    wp201_obj.set_Altitude(600.0)
    wp202_obj = factory.createObjectByName("CMASI", "Waypoint")
    wp202_obj.set_Number(202)
    wp202_obj.set_NextWaypoint(203)
    wp201_obj.set_Speed(30.0)
    wp202_obj.set_Latitude(1.5236)
    wp202_obj.set_Longitude(-132.5274)
    wp202_obj.set_Altitude(600.0)
    wp203_obj = factory.createObjectByName("CMASI", "Waypoint")
    wp203_obj.set_Number(203)
    wp203_obj.set_NextWaypoint(204)
    wp203_obj.set_Speed(20.0)
    wp203_obj.set_Latitude(1.5158)
    wp203_obj.set_Longitude(-132.5203)
    wp203_obj.set_Altitude(600.0)
    wp204_obj = factory.createObjectByName("CMASI", "Waypoint")
    wp204_obj.set_Number(204)
    wp204_obj.set_NextWaypoint(205)
    wp204_obj.set_Speed(30.0)
    wp204_obj.set_Latitude(1.5111)
    wp204_obj.set_Longitude(-132.5306)
    wp204_obj.set_Altitude(600.0)
    wp205_obj = factory.createObjectByName("CMASI", "Waypoint")
    wp205_obj.set_Number(205)
    wp205_obj.set_NextWaypoint(201)
    wp205_obj.set_Speed(20.0)
    wp205_obj.set_Latitude(1.5190)
    wp205_obj.set_Longitude(-132.5299)
    wp205_obj.set_Altitude(600.0)
    mc21_obj = factory.createObjectByName("CMASI", "MissionCommand")
    mc21_obj.set_FirstWaypoint(205)
    mc21_obj.set_CommandID(21)
    mc21_obj.set_VehicleID(2)
    mc21_obj.WaypointList = [wp201_obj, wp202_obj, wp203_obj, wp204_obj, wp205_obj]

    time.sleep(2.0)
    send_to_amase(mc21_obj, socket, client_id)

    # Command air vehicle 3 to go to a point and loiter there with a FigureEight loiter pattern.
    la_obj = factory.createObjectByName("CMASI", "LoiterAction")
    la_obj.set_LoiterType(LoiterType.LoiterType.FigureEight)
    la_obj.set_Axis(45.0)
    la_obj.set_Length(600.0)
    la_obj.set_Direction(LoiterDirection.LoiterDirection.Clockwise)
    la_obj.set_Duration(-1)
    la_obj.set_Airspeed(20.0)
    la_obj.get_Location().set_Latitude(1.5007)
    la_obj.get_Location().set_Longitude(-132.5233)
    la_obj.get_Location().set_Altitude(400.0)
    vac31_obj = factory.createObjectByName("CMASI", "VehicleActionCommand")
    vac31_obj.set_CommandID(31)
    vac31_obj.set_VehicleID(3)
    vac31_obj.VehicleActionList = [la_obj]

    time.sleep(2.0)
    send_to_amase(vac31_obj, socket, client_id)

    ###################################################################################################################
    # Create an AMASE scenario file with all the configuration and initial state information.
    # Save vehicle commands with a "Time" attribute so they can be issued with approximately the same timing as above.
    # -----------------------------------------------------------------------------------------------------------------

    doc = xml.dom.minidom.Document()
    # Create the top-level AMASE element
    amase = doc.createElement("AMASE")
    doc.appendChild(amase)
    # Create the second-level ScenarioData element to add a SimulationView
    scenario_data = doc.createElement("ScenarioData")
    amase.appendChild(scenario_data)
    simulation_view = doc.createElement("SimulationView")
    simulation_view.setAttribute("LongExtent", "0.06")
    simulation_view.setAttribute("Latitude", str(avs_obj.get_Location().get_Latitude()))
    simulation_view.setAttribute("Longitude", str(avs_obj.get_Location().get_Longitude()))
    scenario_data.appendChild(simulation_view)
    # Create the second-level ScenarioEventList and add the AirVehicleConfiguations and AirVehicleStates
    scenario_event_list = doc.createElement("ScenarioEventList")
    amase.appendChild(scenario_event_list)
    # Append AirVehicleConfiguations and AirVehicleStates
    scenario_event_list.appendChild(parseString(lmcp_toprettyxml(avc_obj)).firstChild)
    scenario_event_list.appendChild(parseString(lmcp_toprettyxml(avs_obj)).firstChild)
    scenario_event_list.appendChild(parseString(lmcp_toprettyxml(avc2_obj)).firstChild)
    scenario_event_list.appendChild(parseString(lmcp_toprettyxml(avs2_obj)).firstChild)
    scenario_event_list.appendChild(parseString(lmcp_toprettyxml(avc3_obj)).firstChild)
    scenario_event_list.appendChild(parseString(lmcp_toprettyxml(avs3_obj)).firstChild)
    # Append the commands, each with a "Time" attribute
    dom = parseString(lmcp_toprettyxml(mc11_obj)).firstChild
    dom.setAttribute("Time", "2.0")
    scenario_event_list.appendChild(dom)
    dom = parseString(lmcp_toprettyxml(vac12_obj)).firstChild
    dom.setAttribute("Time", "3.0")
    scenario_event_list.appendChild(dom)
    dom = parseString(lmcp_toprettyxml(mc21_obj)).firstChild
    dom.setAttribute("Time", "5.0")
    scenario_event_list.appendChild(dom)
    dom = parseString(lmcp_toprettyxml(vac31_obj)).firstChild
    dom.setAttribute("Time", "7.0")
    scenario_event_list.appendChild(dom)

    file_handle = open("Scenario_Output.xml", "w")
    file_handle.write(doc.toprettyxml())
    file_handle.close()

    ###################################################################################################################
    # The primary information we get back from AMASE is AirVehicleState.
    # Get state information for each vehicle and print it out.
    # Messages from earlier are still queued, so go through messages until you reach one with time > 7000 ms.
    # -----------------------------------------------------------------------------------------------------------------

    msg_time = 0
    while msg_time <= 7000:
        msg_obj = get_from_amase(socket, factory)
        if msg_obj.FULL_LMCP_TYPE_NAME == 'afrl.cmasi.AirVehicleState':
            msg_time = msg_obj.get_Time()

    id_list = list(range(1, 4))

    print('')
    while len(id_list) > 0:
        msg_obj = get_from_amase(socket, factory)
        if msg_obj.FULL_LMCP_TYPE_NAME == 'afrl.cmasi.AirVehicleState':
            if msg_obj.get_ID() in id_list:
                print('Vehicle ' + str(msg_obj.get_ID()) + ' state information at Time='
                      + str(msg_obj.get_Time()) + ' ms')
                print('\tLat: ' + str(msg_obj.get_Location().get_Latitude()))
                print('\tLon: ' + str(msg_obj.get_Location().get_Longitude()))
                print('\tAlt: ' + str(msg_obj.get_Location().get_Altitude()) + ' m')
                print('\tEnergy: ' + str(msg_obj.get_EnergyAvailable()) + '%\n')
                id_list.remove(msg_obj.get_ID())

    print('Done!')


def send_to_amase(obj, socket, client_id):
    """
    Send an LCMP object to AMASE.

    Keyword arguments:
        obj -- an LMCP message object
        socket -- a ZMQ socket connected to AMASE
        client_id -- the client id for the AMASE socket
    """

    attributes = bytearray(str(obj.FULL_LMCP_TYPE_NAME) + "$lmcp|" + str(obj.FULL_LMCP_TYPE_NAME) + "||0|0$",
                           'ascii')
    smsg = LMCPFactory.packMessage(obj, True)

    sentinel = "+=+=+=+=";
    sentinel += str(len(attributes) + len(smsg));
    sentinel += "#@#@#@#@";

    addressedPayload = attributes;
    addressedPayload.extend(smsg);

    # sentinelized checksum
    val = 0;
    for i in range(0, len(addressedPayload)):
        val += int(addressedPayload[i] & 0xFF);

    footer = "!%!%!%!%" + str(val) + "?^?^?^?^";

    totalmsg = bytearray(sentinel, 'ascii');
    totalmsg.extend(addressedPayload);
    totalmsg.extend(bytearray(footer, 'ascii'));

    socket.send(client_id, flags=zmq.SNDMORE, copy=False)
    socket.send(totalmsg, copy=False)
    print("  Sent:   " + obj.FULL_LMCP_TYPE_NAME)


def get_from_amase(socket, factory):
    """
    Get an LCMP object from AMASE.

    Keyword arguments:
        socket -- a ZMQ socket connected to AMASE
        factory -- an LMCP factory
    """

    client_id, message = socket.recv_multipart()
    address, attributes, msg = message.split(bytearray('$', 'ascii'), 2)
    # msg_format, msg_type, msg_group, entityid, serviceid = attributes.split(bytearray('|', 'ascii'), 4)
    return factory.getObject(msg)


def lmcp_toprettyxml(obj):
    """
    Convert an LCMP object to a string that formats correctly with xml.dom.minidom's toprettyxml().

    Keyword arguments:
        obj -- an LMCP message object
    """

    # toprettyxml() assumes no newlines or whitespace between XML elements,
    # so remove them from what LMCP's toXML() returns.
    return re.sub('\n(\s)*', '', obj.toXML())


if __name__ == '__main__':
    create_and_run_amase_scenario()