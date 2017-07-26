#include "common/struct_defines.h"
#include "lmcp.h"
#include "AbstractGeometry.h"
#include "KeyValuePair.h"
#include "Location3D.h"
#include "PayloadAction.h"
#include "PayloadConfiguration.h"
#include "PayloadState.h"
#include "VehicleAction.h"
#include "Task.h"
#include "SearchTask.h"
#include "AbstractZone.h"
#include "EntityConfiguration.h"
#include "FlightProfile.h"
#include "AirVehicleConfiguration.h"
#include "EntityState.h"
#include "AirVehicleState.h"
#include "Wedge.h"
#include "AreaSearchTask.h"
#include "CameraAction.h"
#include "CameraConfiguration.h"
#include "GimballedPayloadState.h"
#include "CameraState.h"
#include "Circle.h"
#include "GimbalAngleAction.h"
#include "GimbalConfiguration.h"
#include "GimbalScanAction.h"
#include "GimbalStareAction.h"
#include "GimbalState.h"
#include "GoToWaypointAction.h"
#include "KeepInZone.h"
#include "KeepOutZone.h"
#include "LineSearchTask.h"
#include "NavigationAction.h"
#include "LoiterAction.h"
#include "LoiterTask.h"
#include "Waypoint.h"
#include "MissionCommand.h"
#include "MustFlyTask.h"
#include "OperatorSignal.h"
#include "OperatingRegion.h"
#include "AutomationRequest.h"
#include "PointSearchTask.h"
#include "Polygon.h"
#include "Rectangle.h"
#include "RemoveTasks.h"
#include "ServiceStatus.h"
#include "SessionStatus.h"
#include "VehicleActionCommand.h"
#include "VideoStreamAction.h"
#include "VideoStreamConfiguration.h"
#include "VideoStreamState.h"
#include "AutomationResponse.h"
#include "RemoveZones.h"
#include "RemoveEntities.h"
#include "FlightDirectorAction.h"
#include "WeatherReport.h"
#include "FollowPathCommand.h"
#include "PathWaypoint.h"
#include "StopMovementAction.h"
#include "WaypointTransfer.h"
#include "PayloadStowAction.h"
void lmcp_pp(lmcp_object *o) {
    if (o == NULL) {
        return;
    }
    switch (o->type) {
    case 1:
        lmcp_pp_AbstractGeometry((AbstractGeometry*)o);

        break;
    case 2:
        lmcp_pp_KeyValuePair((KeyValuePair*)o);

        break;
    case 3:
        lmcp_pp_Location3D((Location3D*)o);

        break;
    case 4:
        lmcp_pp_PayloadAction((PayloadAction*)o);

        break;
    case 5:
        lmcp_pp_PayloadConfiguration((PayloadConfiguration*)o);

        break;
    case 6:
        lmcp_pp_PayloadState((PayloadState*)o);

        break;
    case 7:
        lmcp_pp_VehicleAction((VehicleAction*)o);

        break;
    case 8:
        lmcp_pp_Task((Task*)o);

        break;
    case 9:
        lmcp_pp_SearchTask((SearchTask*)o);

        break;
    case 10:
        lmcp_pp_AbstractZone((AbstractZone*)o);

        break;
    case 11:
        lmcp_pp_EntityConfiguration((EntityConfiguration*)o);

        break;
    case 12:
        lmcp_pp_FlightProfile((FlightProfile*)o);

        break;
    case 13:
        lmcp_pp_AirVehicleConfiguration((AirVehicleConfiguration*)o);

        break;
    case 14:
        lmcp_pp_EntityState((EntityState*)o);

        break;
    case 15:
        lmcp_pp_AirVehicleState((AirVehicleState*)o);

        break;
    case 16:
        lmcp_pp_Wedge((Wedge*)o);

        break;
    case 17:
        lmcp_pp_AreaSearchTask((AreaSearchTask*)o);

        break;
    case 18:
        lmcp_pp_CameraAction((CameraAction*)o);

        break;
    case 19:
        lmcp_pp_CameraConfiguration((CameraConfiguration*)o);

        break;
    case 20:
        lmcp_pp_GimballedPayloadState((GimballedPayloadState*)o);

        break;
    case 21:
        lmcp_pp_CameraState((CameraState*)o);

        break;
    case 22:
        lmcp_pp_Circle((Circle*)o);

        break;
    case 23:
        lmcp_pp_GimbalAngleAction((GimbalAngleAction*)o);

        break;
    case 24:
        lmcp_pp_GimbalConfiguration((GimbalConfiguration*)o);

        break;
    case 25:
        lmcp_pp_GimbalScanAction((GimbalScanAction*)o);

        break;
    case 26:
        lmcp_pp_GimbalStareAction((GimbalStareAction*)o);

        break;
    case 27:
        lmcp_pp_GimbalState((GimbalState*)o);

        break;
    case 28:
        lmcp_pp_GoToWaypointAction((GoToWaypointAction*)o);

        break;
    case 29:
        lmcp_pp_KeepInZone((KeepInZone*)o);

        break;
    case 30:
        lmcp_pp_KeepOutZone((KeepOutZone*)o);

        break;
    case 31:
        lmcp_pp_LineSearchTask((LineSearchTask*)o);

        break;
    case 32:
        lmcp_pp_NavigationAction((NavigationAction*)o);

        break;
    case 33:
        lmcp_pp_LoiterAction((LoiterAction*)o);

        break;
    case 34:
        lmcp_pp_LoiterTask((LoiterTask*)o);

        break;
    case 35:
        lmcp_pp_Waypoint((Waypoint*)o);

        break;
    case 36:
        lmcp_pp_MissionCommand((MissionCommand*)o);

        break;
    case 37:
        lmcp_pp_MustFlyTask((MustFlyTask*)o);

        break;
    case 38:
        lmcp_pp_OperatorSignal((OperatorSignal*)o);

        break;
    case 39:
        lmcp_pp_OperatingRegion((OperatingRegion*)o);

        break;
    case 40:
        lmcp_pp_AutomationRequest((AutomationRequest*)o);

        break;
    case 41:
        lmcp_pp_PointSearchTask((PointSearchTask*)o);

        break;
    case 42:
        lmcp_pp_Polygon((Polygon*)o);

        break;
    case 43:
        lmcp_pp_Rectangle((Rectangle*)o);

        break;
    case 44:
        lmcp_pp_RemoveTasks((RemoveTasks*)o);

        break;
    case 45:
        lmcp_pp_ServiceStatus((ServiceStatus*)o);

        break;
    case 46:
        lmcp_pp_SessionStatus((SessionStatus*)o);

        break;
    case 47:
        lmcp_pp_VehicleActionCommand((VehicleActionCommand*)o);

        break;
    case 48:
        lmcp_pp_VideoStreamAction((VideoStreamAction*)o);

        break;
    case 49:
        lmcp_pp_VideoStreamConfiguration((VideoStreamConfiguration*)o);

        break;
    case 50:
        lmcp_pp_VideoStreamState((VideoStreamState*)o);

        break;
    case 51:
        lmcp_pp_AutomationResponse((AutomationResponse*)o);

        break;
    case 52:
        lmcp_pp_RemoveZones((RemoveZones*)o);

        break;
    case 53:
        lmcp_pp_RemoveEntities((RemoveEntities*)o);

        break;
    case 54:
        lmcp_pp_FlightDirectorAction((FlightDirectorAction*)o);

        break;
    case 55:
        lmcp_pp_WeatherReport((WeatherReport*)o);

        break;
    case 56:
        lmcp_pp_FollowPathCommand((FollowPathCommand*)o);

        break;
    case 57:
        lmcp_pp_PathWaypoint((PathWaypoint*)o);

        break;
    case 58:
        lmcp_pp_StopMovementAction((StopMovementAction*)o);

        break;
    case 59:
        lmcp_pp_WaypointTransfer((WaypointTransfer*)o);

        break;
    case 60:
        lmcp_pp_PayloadStowAction((PayloadStowAction*)o);

        break;
    default:
        return;
    }
}
uint32_t lmcp_msgsize(lmcp_object* o) {
    return 8 + lmcp_packsize(o);
}
uint32_t lmcp_packsize(lmcp_object* o) {
    switch (o->type) {
    case 1:
        return 15 + lmcp_packsize_AbstractGeometry((AbstractGeometry*)o);

        break;
    case 2:
        return 15 + lmcp_packsize_KeyValuePair((KeyValuePair*)o);

        break;
    case 3:
        return 15 + lmcp_packsize_Location3D((Location3D*)o);

        break;
    case 4:
        return 15 + lmcp_packsize_PayloadAction((PayloadAction*)o);

        break;
    case 5:
        return 15 + lmcp_packsize_PayloadConfiguration((PayloadConfiguration*)o);

        break;
    case 6:
        return 15 + lmcp_packsize_PayloadState((PayloadState*)o);

        break;
    case 7:
        return 15 + lmcp_packsize_VehicleAction((VehicleAction*)o);

        break;
    case 8:
        return 15 + lmcp_packsize_Task((Task*)o);

        break;
    case 9:
        return 15 + lmcp_packsize_SearchTask((SearchTask*)o);

        break;
    case 10:
        return 15 + lmcp_packsize_AbstractZone((AbstractZone*)o);

        break;
    case 11:
        return 15 + lmcp_packsize_EntityConfiguration((EntityConfiguration*)o);

        break;
    case 12:
        return 15 + lmcp_packsize_FlightProfile((FlightProfile*)o);

        break;
    case 13:
        return 15 + lmcp_packsize_AirVehicleConfiguration((AirVehicleConfiguration*)o);

        break;
    case 14:
        return 15 + lmcp_packsize_EntityState((EntityState*)o);

        break;
    case 15:
        return 15 + lmcp_packsize_AirVehicleState((AirVehicleState*)o);

        break;
    case 16:
        return 15 + lmcp_packsize_Wedge((Wedge*)o);

        break;
    case 17:
        return 15 + lmcp_packsize_AreaSearchTask((AreaSearchTask*)o);

        break;
    case 18:
        return 15 + lmcp_packsize_CameraAction((CameraAction*)o);

        break;
    case 19:
        return 15 + lmcp_packsize_CameraConfiguration((CameraConfiguration*)o);

        break;
    case 20:
        return 15 + lmcp_packsize_GimballedPayloadState((GimballedPayloadState*)o);

        break;
    case 21:
        return 15 + lmcp_packsize_CameraState((CameraState*)o);

        break;
    case 22:
        return 15 + lmcp_packsize_Circle((Circle*)o);

        break;
    case 23:
        return 15 + lmcp_packsize_GimbalAngleAction((GimbalAngleAction*)o);

        break;
    case 24:
        return 15 + lmcp_packsize_GimbalConfiguration((GimbalConfiguration*)o);

        break;
    case 25:
        return 15 + lmcp_packsize_GimbalScanAction((GimbalScanAction*)o);

        break;
    case 26:
        return 15 + lmcp_packsize_GimbalStareAction((GimbalStareAction*)o);

        break;
    case 27:
        return 15 + lmcp_packsize_GimbalState((GimbalState*)o);

        break;
    case 28:
        return 15 + lmcp_packsize_GoToWaypointAction((GoToWaypointAction*)o);

        break;
    case 29:
        return 15 + lmcp_packsize_KeepInZone((KeepInZone*)o);

        break;
    case 30:
        return 15 + lmcp_packsize_KeepOutZone((KeepOutZone*)o);

        break;
    case 31:
        return 15 + lmcp_packsize_LineSearchTask((LineSearchTask*)o);

        break;
    case 32:
        return 15 + lmcp_packsize_NavigationAction((NavigationAction*)o);

        break;
    case 33:
        return 15 + lmcp_packsize_LoiterAction((LoiterAction*)o);

        break;
    case 34:
        return 15 + lmcp_packsize_LoiterTask((LoiterTask*)o);

        break;
    case 35:
        return 15 + lmcp_packsize_Waypoint((Waypoint*)o);

        break;
    case 36:
        return 15 + lmcp_packsize_MissionCommand((MissionCommand*)o);

        break;
    case 37:
        return 15 + lmcp_packsize_MustFlyTask((MustFlyTask*)o);

        break;
    case 38:
        return 15 + lmcp_packsize_OperatorSignal((OperatorSignal*)o);

        break;
    case 39:
        return 15 + lmcp_packsize_OperatingRegion((OperatingRegion*)o);

        break;
    case 40:
        return 15 + lmcp_packsize_AutomationRequest((AutomationRequest*)o);

        break;
    case 41:
        return 15 + lmcp_packsize_PointSearchTask((PointSearchTask*)o);

        break;
    case 42:
        return 15 + lmcp_packsize_Polygon((Polygon*)o);

        break;
    case 43:
        return 15 + lmcp_packsize_Rectangle((Rectangle*)o);

        break;
    case 44:
        return 15 + lmcp_packsize_RemoveTasks((RemoveTasks*)o);

        break;
    case 45:
        return 15 + lmcp_packsize_ServiceStatus((ServiceStatus*)o);

        break;
    case 46:
        return 15 + lmcp_packsize_SessionStatus((SessionStatus*)o);

        break;
    case 47:
        return 15 + lmcp_packsize_VehicleActionCommand((VehicleActionCommand*)o);

        break;
    case 48:
        return 15 + lmcp_packsize_VideoStreamAction((VideoStreamAction*)o);

        break;
    case 49:
        return 15 + lmcp_packsize_VideoStreamConfiguration((VideoStreamConfiguration*)o);

        break;
    case 50:
        return 15 + lmcp_packsize_VideoStreamState((VideoStreamState*)o);

        break;
    case 51:
        return 15 + lmcp_packsize_AutomationResponse((AutomationResponse*)o);

        break;
    case 52:
        return 15 + lmcp_packsize_RemoveZones((RemoveZones*)o);

        break;
    case 53:
        return 15 + lmcp_packsize_RemoveEntities((RemoveEntities*)o);

        break;
    case 54:
        return 15 + lmcp_packsize_FlightDirectorAction((FlightDirectorAction*)o);

        break;
    case 55:
        return 15 + lmcp_packsize_WeatherReport((WeatherReport*)o);

        break;
    case 56:
        return 15 + lmcp_packsize_FollowPathCommand((FollowPathCommand*)o);

        break;
    case 57:
        return 15 + lmcp_packsize_PathWaypoint((PathWaypoint*)o);

        break;
    case 58:
        return 15 + lmcp_packsize_StopMovementAction((StopMovementAction*)o);

        break;
    case 59:
        return 15 + lmcp_packsize_WaypointTransfer((WaypointTransfer*)o);

        break;
    case 60:
        return 15 + lmcp_packsize_PayloadStowAction((PayloadStowAction*)o);

        break;
    default:
        return 0;
    }
}
void lmcp_free(lmcp_object *o) {
    if (o == NULL) {
        return;
    }
    switch (o->type) {
    case 1:
        lmcp_free_AbstractGeometry((AbstractGeometry*)o, 1);

        break;
    case 2:
        lmcp_free_KeyValuePair((KeyValuePair*)o, 1);

        break;
    case 3:
        lmcp_free_Location3D((Location3D*)o, 1);

        break;
    case 4:
        lmcp_free_PayloadAction((PayloadAction*)o, 1);

        break;
    case 5:
        lmcp_free_PayloadConfiguration((PayloadConfiguration*)o, 1);

        break;
    case 6:
        lmcp_free_PayloadState((PayloadState*)o, 1);

        break;
    case 7:
        lmcp_free_VehicleAction((VehicleAction*)o, 1);

        break;
    case 8:
        lmcp_free_Task((Task*)o, 1);

        break;
    case 9:
        lmcp_free_SearchTask((SearchTask*)o, 1);

        break;
    case 10:
        lmcp_free_AbstractZone((AbstractZone*)o, 1);

        break;
    case 11:
        lmcp_free_EntityConfiguration((EntityConfiguration*)o, 1);

        break;
    case 12:
        lmcp_free_FlightProfile((FlightProfile*)o, 1);

        break;
    case 13:
        lmcp_free_AirVehicleConfiguration((AirVehicleConfiguration*)o, 1);

        break;
    case 14:
        lmcp_free_EntityState((EntityState*)o, 1);

        break;
    case 15:
        lmcp_free_AirVehicleState((AirVehicleState*)o, 1);

        break;
    case 16:
        lmcp_free_Wedge((Wedge*)o, 1);

        break;
    case 17:
        lmcp_free_AreaSearchTask((AreaSearchTask*)o, 1);

        break;
    case 18:
        lmcp_free_CameraAction((CameraAction*)o, 1);

        break;
    case 19:
        lmcp_free_CameraConfiguration((CameraConfiguration*)o, 1);

        break;
    case 20:
        lmcp_free_GimballedPayloadState((GimballedPayloadState*)o, 1);

        break;
    case 21:
        lmcp_free_CameraState((CameraState*)o, 1);

        break;
    case 22:
        lmcp_free_Circle((Circle*)o, 1);

        break;
    case 23:
        lmcp_free_GimbalAngleAction((GimbalAngleAction*)o, 1);

        break;
    case 24:
        lmcp_free_GimbalConfiguration((GimbalConfiguration*)o, 1);

        break;
    case 25:
        lmcp_free_GimbalScanAction((GimbalScanAction*)o, 1);

        break;
    case 26:
        lmcp_free_GimbalStareAction((GimbalStareAction*)o, 1);

        break;
    case 27:
        lmcp_free_GimbalState((GimbalState*)o, 1);

        break;
    case 28:
        lmcp_free_GoToWaypointAction((GoToWaypointAction*)o, 1);

        break;
    case 29:
        lmcp_free_KeepInZone((KeepInZone*)o, 1);

        break;
    case 30:
        lmcp_free_KeepOutZone((KeepOutZone*)o, 1);

        break;
    case 31:
        lmcp_free_LineSearchTask((LineSearchTask*)o, 1);

        break;
    case 32:
        lmcp_free_NavigationAction((NavigationAction*)o, 1);

        break;
    case 33:
        lmcp_free_LoiterAction((LoiterAction*)o, 1);

        break;
    case 34:
        lmcp_free_LoiterTask((LoiterTask*)o, 1);

        break;
    case 35:
        lmcp_free_Waypoint((Waypoint*)o, 1);

        break;
    case 36:
        lmcp_free_MissionCommand((MissionCommand*)o, 1);

        break;
    case 37:
        lmcp_free_MustFlyTask((MustFlyTask*)o, 1);

        break;
    case 38:
        lmcp_free_OperatorSignal((OperatorSignal*)o, 1);

        break;
    case 39:
        lmcp_free_OperatingRegion((OperatingRegion*)o, 1);

        break;
    case 40:
        lmcp_free_AutomationRequest((AutomationRequest*)o, 1);

        break;
    case 41:
        lmcp_free_PointSearchTask((PointSearchTask*)o, 1);

        break;
    case 42:
        lmcp_free_Polygon((Polygon*)o, 1);

        break;
    case 43:
        lmcp_free_Rectangle((Rectangle*)o, 1);

        break;
    case 44:
        lmcp_free_RemoveTasks((RemoveTasks*)o, 1);

        break;
    case 45:
        lmcp_free_ServiceStatus((ServiceStatus*)o, 1);

        break;
    case 46:
        lmcp_free_SessionStatus((SessionStatus*)o, 1);

        break;
    case 47:
        lmcp_free_VehicleActionCommand((VehicleActionCommand*)o, 1);

        break;
    case 48:
        lmcp_free_VideoStreamAction((VideoStreamAction*)o, 1);

        break;
    case 49:
        lmcp_free_VideoStreamConfiguration((VideoStreamConfiguration*)o, 1);

        break;
    case 50:
        lmcp_free_VideoStreamState((VideoStreamState*)o, 1);

        break;
    case 51:
        lmcp_free_AutomationResponse((AutomationResponse*)o, 1);

        break;
    case 52:
        lmcp_free_RemoveZones((RemoveZones*)o, 1);

        break;
    case 53:
        lmcp_free_RemoveEntities((RemoveEntities*)o, 1);

        break;
    case 54:
        lmcp_free_FlightDirectorAction((FlightDirectorAction*)o, 1);

        break;
    case 55:
        lmcp_free_WeatherReport((WeatherReport*)o, 1);

        break;
    case 56:
        lmcp_free_FollowPathCommand((FollowPathCommand*)o, 1);

        break;
    case 57:
        lmcp_free_PathWaypoint((PathWaypoint*)o, 1);

        break;
    case 58:
        lmcp_free_StopMovementAction((StopMovementAction*)o, 1);

        break;
    case 59:
        lmcp_free_WaypointTransfer((WaypointTransfer*)o, 1);

        break;
    case 60:
        lmcp_free_PayloadStowAction((PayloadStowAction*)o, 1);

        break;
    default:
        return;
    }
}
void lmcp_make_msg(uint8_t* buf, lmcp_object* o) {
    buf[0] = 'L';
    buf[1] = 'M';
    buf[2] = 'C';
    buf[3] = 'P';
    lmcp_pack_uint32_t(buf+4, lmcp_packsize(o));
    lmcp_pack(buf + 8, o);
}
int lmcp_process_msg(uint8_t** inb, size_t size, lmcp_object **o) {
    if (size < 8) {
        return -1;
    }
    if (inb == NULL || *inb == NULL) {
        return -1;
    }
    if ((*inb)[0] != 'L' || (*inb)[1] != 'M' || (*inb)[2] != 'C' || (*inb)[3] != 'P') {
        return -1;
    }
    *inb += 4;
    size_t s = 4;
    uint32_t msglen;
    CHECK(lmcp_unpack_uint32_t(inb, &s, &msglen))
    if (size < (msglen + 8)) {
        return -1;
    }
    CHECK(lmcp_unpack(inb, msglen, o))
    return 0;
}
int lmcp_unpack(uint8_t** inb, size_t size, lmcp_object **o) {
    if (o == NULL) return -1;
    size_t* size_remain = &size;
    int isnull;
    uint32_t objtype;
    uint16_t objseries;
    char seriesname[8];
    isnull = lmcp_unpack_structheader(inb, size_remain, seriesname, &objtype, &objseries);
    if (isnull == -1) {
        return -1;
    }
    switch (objtype) {
    case 1:
        lmcp_init_AbstractGeometry((AbstractGeometry**)o);
        CHECK(lmcp_unpack_AbstractGeometry(inb, size_remain, (AbstractGeometry*)(*o)))

        break;
    case 2:
        lmcp_init_KeyValuePair((KeyValuePair**)o);
        CHECK(lmcp_unpack_KeyValuePair(inb, size_remain, (KeyValuePair*)(*o)))

        break;
    case 3:
        lmcp_init_Location3D((Location3D**)o);
        CHECK(lmcp_unpack_Location3D(inb, size_remain, (Location3D*)(*o)))

        break;
    case 4:
        lmcp_init_PayloadAction((PayloadAction**)o);
        CHECK(lmcp_unpack_PayloadAction(inb, size_remain, (PayloadAction*)(*o)))

        break;
    case 5:
        lmcp_init_PayloadConfiguration((PayloadConfiguration**)o);
        CHECK(lmcp_unpack_PayloadConfiguration(inb, size_remain, (PayloadConfiguration*)(*o)))

        break;
    case 6:
        lmcp_init_PayloadState((PayloadState**)o);
        CHECK(lmcp_unpack_PayloadState(inb, size_remain, (PayloadState*)(*o)))

        break;
    case 7:
        lmcp_init_VehicleAction((VehicleAction**)o);
        CHECK(lmcp_unpack_VehicleAction(inb, size_remain, (VehicleAction*)(*o)))

        break;
    case 8:
        lmcp_init_Task((Task**)o);
        CHECK(lmcp_unpack_Task(inb, size_remain, (Task*)(*o)))

        break;
    case 9:
        lmcp_init_SearchTask((SearchTask**)o);
        CHECK(lmcp_unpack_SearchTask(inb, size_remain, (SearchTask*)(*o)))

        break;
    case 10:
        lmcp_init_AbstractZone((AbstractZone**)o);
        CHECK(lmcp_unpack_AbstractZone(inb, size_remain, (AbstractZone*)(*o)))

        break;
    case 11:
        lmcp_init_EntityConfiguration((EntityConfiguration**)o);
        CHECK(lmcp_unpack_EntityConfiguration(inb, size_remain, (EntityConfiguration*)(*o)))

        break;
    case 12:
        lmcp_init_FlightProfile((FlightProfile**)o);
        CHECK(lmcp_unpack_FlightProfile(inb, size_remain, (FlightProfile*)(*o)))

        break;
    case 13:
        lmcp_init_AirVehicleConfiguration((AirVehicleConfiguration**)o);
        CHECK(lmcp_unpack_AirVehicleConfiguration(inb, size_remain, (AirVehicleConfiguration*)(*o)))

        break;
    case 14:
        lmcp_init_EntityState((EntityState**)o);
        CHECK(lmcp_unpack_EntityState(inb, size_remain, (EntityState*)(*o)))

        break;
    case 15:
        lmcp_init_AirVehicleState((AirVehicleState**)o);
        CHECK(lmcp_unpack_AirVehicleState(inb, size_remain, (AirVehicleState*)(*o)))

        break;
    case 16:
        lmcp_init_Wedge((Wedge**)o);
        CHECK(lmcp_unpack_Wedge(inb, size_remain, (Wedge*)(*o)))

        break;
    case 17:
        lmcp_init_AreaSearchTask((AreaSearchTask**)o);
        CHECK(lmcp_unpack_AreaSearchTask(inb, size_remain, (AreaSearchTask*)(*o)))

        break;
    case 18:
        lmcp_init_CameraAction((CameraAction**)o);
        CHECK(lmcp_unpack_CameraAction(inb, size_remain, (CameraAction*)(*o)))

        break;
    case 19:
        lmcp_init_CameraConfiguration((CameraConfiguration**)o);
        CHECK(lmcp_unpack_CameraConfiguration(inb, size_remain, (CameraConfiguration*)(*o)))

        break;
    case 20:
        lmcp_init_GimballedPayloadState((GimballedPayloadState**)o);
        CHECK(lmcp_unpack_GimballedPayloadState(inb, size_remain, (GimballedPayloadState*)(*o)))

        break;
    case 21:
        lmcp_init_CameraState((CameraState**)o);
        CHECK(lmcp_unpack_CameraState(inb, size_remain, (CameraState*)(*o)))

        break;
    case 22:
        lmcp_init_Circle((Circle**)o);
        CHECK(lmcp_unpack_Circle(inb, size_remain, (Circle*)(*o)))

        break;
    case 23:
        lmcp_init_GimbalAngleAction((GimbalAngleAction**)o);
        CHECK(lmcp_unpack_GimbalAngleAction(inb, size_remain, (GimbalAngleAction*)(*o)))

        break;
    case 24:
        lmcp_init_GimbalConfiguration((GimbalConfiguration**)o);
        CHECK(lmcp_unpack_GimbalConfiguration(inb, size_remain, (GimbalConfiguration*)(*o)))

        break;
    case 25:
        lmcp_init_GimbalScanAction((GimbalScanAction**)o);
        CHECK(lmcp_unpack_GimbalScanAction(inb, size_remain, (GimbalScanAction*)(*o)))

        break;
    case 26:
        lmcp_init_GimbalStareAction((GimbalStareAction**)o);
        CHECK(lmcp_unpack_GimbalStareAction(inb, size_remain, (GimbalStareAction*)(*o)))

        break;
    case 27:
        lmcp_init_GimbalState((GimbalState**)o);
        CHECK(lmcp_unpack_GimbalState(inb, size_remain, (GimbalState*)(*o)))

        break;
    case 28:
        lmcp_init_GoToWaypointAction((GoToWaypointAction**)o);
        CHECK(lmcp_unpack_GoToWaypointAction(inb, size_remain, (GoToWaypointAction*)(*o)))

        break;
    case 29:
        lmcp_init_KeepInZone((KeepInZone**)o);
        CHECK(lmcp_unpack_KeepInZone(inb, size_remain, (KeepInZone*)(*o)))

        break;
    case 30:
        lmcp_init_KeepOutZone((KeepOutZone**)o);
        CHECK(lmcp_unpack_KeepOutZone(inb, size_remain, (KeepOutZone*)(*o)))

        break;
    case 31:
        lmcp_init_LineSearchTask((LineSearchTask**)o);
        CHECK(lmcp_unpack_LineSearchTask(inb, size_remain, (LineSearchTask*)(*o)))

        break;
    case 32:
        lmcp_init_NavigationAction((NavigationAction**)o);
        CHECK(lmcp_unpack_NavigationAction(inb, size_remain, (NavigationAction*)(*o)))

        break;
    case 33:
        lmcp_init_LoiterAction((LoiterAction**)o);
        CHECK(lmcp_unpack_LoiterAction(inb, size_remain, (LoiterAction*)(*o)))

        break;
    case 34:
        lmcp_init_LoiterTask((LoiterTask**)o);
        CHECK(lmcp_unpack_LoiterTask(inb, size_remain, (LoiterTask*)(*o)))

        break;
    case 35:
        lmcp_init_Waypoint((Waypoint**)o);
        CHECK(lmcp_unpack_Waypoint(inb, size_remain, (Waypoint*)(*o)))

        break;
    case 36:
        lmcp_init_MissionCommand((MissionCommand**)o);
        CHECK(lmcp_unpack_MissionCommand(inb, size_remain, (MissionCommand*)(*o)))

        break;
    case 37:
        lmcp_init_MustFlyTask((MustFlyTask**)o);
        CHECK(lmcp_unpack_MustFlyTask(inb, size_remain, (MustFlyTask*)(*o)))

        break;
    case 38:
        lmcp_init_OperatorSignal((OperatorSignal**)o);
        CHECK(lmcp_unpack_OperatorSignal(inb, size_remain, (OperatorSignal*)(*o)))

        break;
    case 39:
        lmcp_init_OperatingRegion((OperatingRegion**)o);
        CHECK(lmcp_unpack_OperatingRegion(inb, size_remain, (OperatingRegion*)(*o)))

        break;
    case 40:
        lmcp_init_AutomationRequest((AutomationRequest**)o);
        CHECK(lmcp_unpack_AutomationRequest(inb, size_remain, (AutomationRequest*)(*o)))

        break;
    case 41:
        lmcp_init_PointSearchTask((PointSearchTask**)o);
        CHECK(lmcp_unpack_PointSearchTask(inb, size_remain, (PointSearchTask*)(*o)))

        break;
    case 42:
        lmcp_init_Polygon((Polygon**)o);
        CHECK(lmcp_unpack_Polygon(inb, size_remain, (Polygon*)(*o)))

        break;
    case 43:
        lmcp_init_Rectangle((Rectangle**)o);
        CHECK(lmcp_unpack_Rectangle(inb, size_remain, (Rectangle*)(*o)))

        break;
    case 44:
        lmcp_init_RemoveTasks((RemoveTasks**)o);
        CHECK(lmcp_unpack_RemoveTasks(inb, size_remain, (RemoveTasks*)(*o)))

        break;
    case 45:
        lmcp_init_ServiceStatus((ServiceStatus**)o);
        CHECK(lmcp_unpack_ServiceStatus(inb, size_remain, (ServiceStatus*)(*o)))

        break;
    case 46:
        lmcp_init_SessionStatus((SessionStatus**)o);
        CHECK(lmcp_unpack_SessionStatus(inb, size_remain, (SessionStatus*)(*o)))

        break;
    case 47:
        lmcp_init_VehicleActionCommand((VehicleActionCommand**)o);
        CHECK(lmcp_unpack_VehicleActionCommand(inb, size_remain, (VehicleActionCommand*)(*o)))

        break;
    case 48:
        lmcp_init_VideoStreamAction((VideoStreamAction**)o);
        CHECK(lmcp_unpack_VideoStreamAction(inb, size_remain, (VideoStreamAction*)(*o)))

        break;
    case 49:
        lmcp_init_VideoStreamConfiguration((VideoStreamConfiguration**)o);
        CHECK(lmcp_unpack_VideoStreamConfiguration(inb, size_remain, (VideoStreamConfiguration*)(*o)))

        break;
    case 50:
        lmcp_init_VideoStreamState((VideoStreamState**)o);
        CHECK(lmcp_unpack_VideoStreamState(inb, size_remain, (VideoStreamState*)(*o)))

        break;
    case 51:
        lmcp_init_AutomationResponse((AutomationResponse**)o);
        CHECK(lmcp_unpack_AutomationResponse(inb, size_remain, (AutomationResponse*)(*o)))

        break;
    case 52:
        lmcp_init_RemoveZones((RemoveZones**)o);
        CHECK(lmcp_unpack_RemoveZones(inb, size_remain, (RemoveZones*)(*o)))

        break;
    case 53:
        lmcp_init_RemoveEntities((RemoveEntities**)o);
        CHECK(lmcp_unpack_RemoveEntities(inb, size_remain, (RemoveEntities*)(*o)))

        break;
    case 54:
        lmcp_init_FlightDirectorAction((FlightDirectorAction**)o);
        CHECK(lmcp_unpack_FlightDirectorAction(inb, size_remain, (FlightDirectorAction*)(*o)))

        break;
    case 55:
        lmcp_init_WeatherReport((WeatherReport**)o);
        CHECK(lmcp_unpack_WeatherReport(inb, size_remain, (WeatherReport*)(*o)))

        break;
    case 56:
        lmcp_init_FollowPathCommand((FollowPathCommand**)o);
        CHECK(lmcp_unpack_FollowPathCommand(inb, size_remain, (FollowPathCommand*)(*o)))

        break;
    case 57:
        lmcp_init_PathWaypoint((PathWaypoint**)o);
        CHECK(lmcp_unpack_PathWaypoint(inb, size_remain, (PathWaypoint*)(*o)))

        break;
    case 58:
        lmcp_init_StopMovementAction((StopMovementAction**)o);
        CHECK(lmcp_unpack_StopMovementAction(inb, size_remain, (StopMovementAction*)(*o)))

        break;
    case 59:
        lmcp_init_WaypointTransfer((WaypointTransfer**)o);
        CHECK(lmcp_unpack_WaypointTransfer(inb, size_remain, (WaypointTransfer*)(*o)))

        break;
    case 60:
        lmcp_init_PayloadStowAction((PayloadStowAction**)o);
        CHECK(lmcp_unpack_PayloadStowAction(inb, size_remain, (PayloadStowAction*)(*o)))

        break;
    default:
        return 0;
    }
    return 0;
}
uint32_t lmcp_pack(uint8_t* buf, lmcp_object* o) {
    uint8_t* outb = buf;
    switch (o->type) {
    case 1:
        outb += lmcp_pack_AbstractGeometry_header(outb, (AbstractGeometry*)o);
        outb += lmcp_pack_AbstractGeometry(outb, (AbstractGeometry*)o);
        return (outb - buf);

        break;
    case 2:
        outb += lmcp_pack_KeyValuePair_header(outb, (KeyValuePair*)o);
        outb += lmcp_pack_KeyValuePair(outb, (KeyValuePair*)o);
        return (outb - buf);

        break;
    case 3:
        outb += lmcp_pack_Location3D_header(outb, (Location3D*)o);
        outb += lmcp_pack_Location3D(outb, (Location3D*)o);
        return (outb - buf);

        break;
    case 4:
        outb += lmcp_pack_PayloadAction_header(outb, (PayloadAction*)o);
        outb += lmcp_pack_PayloadAction(outb, (PayloadAction*)o);
        return (outb - buf);

        break;
    case 5:
        outb += lmcp_pack_PayloadConfiguration_header(outb, (PayloadConfiguration*)o);
        outb += lmcp_pack_PayloadConfiguration(outb, (PayloadConfiguration*)o);
        return (outb - buf);

        break;
    case 6:
        outb += lmcp_pack_PayloadState_header(outb, (PayloadState*)o);
        outb += lmcp_pack_PayloadState(outb, (PayloadState*)o);
        return (outb - buf);

        break;
    case 7:
        outb += lmcp_pack_VehicleAction_header(outb, (VehicleAction*)o);
        outb += lmcp_pack_VehicleAction(outb, (VehicleAction*)o);
        return (outb - buf);

        break;
    case 8:
        outb += lmcp_pack_Task_header(outb, (Task*)o);
        outb += lmcp_pack_Task(outb, (Task*)o);
        return (outb - buf);

        break;
    case 9:
        outb += lmcp_pack_SearchTask_header(outb, (SearchTask*)o);
        outb += lmcp_pack_SearchTask(outb, (SearchTask*)o);
        return (outb - buf);

        break;
    case 10:
        outb += lmcp_pack_AbstractZone_header(outb, (AbstractZone*)o);
        outb += lmcp_pack_AbstractZone(outb, (AbstractZone*)o);
        return (outb - buf);

        break;
    case 11:
        outb += lmcp_pack_EntityConfiguration_header(outb, (EntityConfiguration*)o);
        outb += lmcp_pack_EntityConfiguration(outb, (EntityConfiguration*)o);
        return (outb - buf);

        break;
    case 12:
        outb += lmcp_pack_FlightProfile_header(outb, (FlightProfile*)o);
        outb += lmcp_pack_FlightProfile(outb, (FlightProfile*)o);
        return (outb - buf);

        break;
    case 13:
        outb += lmcp_pack_AirVehicleConfiguration_header(outb, (AirVehicleConfiguration*)o);
        outb += lmcp_pack_AirVehicleConfiguration(outb, (AirVehicleConfiguration*)o);
        return (outb - buf);

        break;
    case 14:
        outb += lmcp_pack_EntityState_header(outb, (EntityState*)o);
        outb += lmcp_pack_EntityState(outb, (EntityState*)o);
        return (outb - buf);

        break;
    case 15:
        outb += lmcp_pack_AirVehicleState_header(outb, (AirVehicleState*)o);
        outb += lmcp_pack_AirVehicleState(outb, (AirVehicleState*)o);
        return (outb - buf);

        break;
    case 16:
        outb += lmcp_pack_Wedge_header(outb, (Wedge*)o);
        outb += lmcp_pack_Wedge(outb, (Wedge*)o);
        return (outb - buf);

        break;
    case 17:
        outb += lmcp_pack_AreaSearchTask_header(outb, (AreaSearchTask*)o);
        outb += lmcp_pack_AreaSearchTask(outb, (AreaSearchTask*)o);
        return (outb - buf);

        break;
    case 18:
        outb += lmcp_pack_CameraAction_header(outb, (CameraAction*)o);
        outb += lmcp_pack_CameraAction(outb, (CameraAction*)o);
        return (outb - buf);

        break;
    case 19:
        outb += lmcp_pack_CameraConfiguration_header(outb, (CameraConfiguration*)o);
        outb += lmcp_pack_CameraConfiguration(outb, (CameraConfiguration*)o);
        return (outb - buf);

        break;
    case 20:
        outb += lmcp_pack_GimballedPayloadState_header(outb, (GimballedPayloadState*)o);
        outb += lmcp_pack_GimballedPayloadState(outb, (GimballedPayloadState*)o);
        return (outb - buf);

        break;
    case 21:
        outb += lmcp_pack_CameraState_header(outb, (CameraState*)o);
        outb += lmcp_pack_CameraState(outb, (CameraState*)o);
        return (outb - buf);

        break;
    case 22:
        outb += lmcp_pack_Circle_header(outb, (Circle*)o);
        outb += lmcp_pack_Circle(outb, (Circle*)o);
        return (outb - buf);

        break;
    case 23:
        outb += lmcp_pack_GimbalAngleAction_header(outb, (GimbalAngleAction*)o);
        outb += lmcp_pack_GimbalAngleAction(outb, (GimbalAngleAction*)o);
        return (outb - buf);

        break;
    case 24:
        outb += lmcp_pack_GimbalConfiguration_header(outb, (GimbalConfiguration*)o);
        outb += lmcp_pack_GimbalConfiguration(outb, (GimbalConfiguration*)o);
        return (outb - buf);

        break;
    case 25:
        outb += lmcp_pack_GimbalScanAction_header(outb, (GimbalScanAction*)o);
        outb += lmcp_pack_GimbalScanAction(outb, (GimbalScanAction*)o);
        return (outb - buf);

        break;
    case 26:
        outb += lmcp_pack_GimbalStareAction_header(outb, (GimbalStareAction*)o);
        outb += lmcp_pack_GimbalStareAction(outb, (GimbalStareAction*)o);
        return (outb - buf);

        break;
    case 27:
        outb += lmcp_pack_GimbalState_header(outb, (GimbalState*)o);
        outb += lmcp_pack_GimbalState(outb, (GimbalState*)o);
        return (outb - buf);

        break;
    case 28:
        outb += lmcp_pack_GoToWaypointAction_header(outb, (GoToWaypointAction*)o);
        outb += lmcp_pack_GoToWaypointAction(outb, (GoToWaypointAction*)o);
        return (outb - buf);

        break;
    case 29:
        outb += lmcp_pack_KeepInZone_header(outb, (KeepInZone*)o);
        outb += lmcp_pack_KeepInZone(outb, (KeepInZone*)o);
        return (outb - buf);

        break;
    case 30:
        outb += lmcp_pack_KeepOutZone_header(outb, (KeepOutZone*)o);
        outb += lmcp_pack_KeepOutZone(outb, (KeepOutZone*)o);
        return (outb - buf);

        break;
    case 31:
        outb += lmcp_pack_LineSearchTask_header(outb, (LineSearchTask*)o);
        outb += lmcp_pack_LineSearchTask(outb, (LineSearchTask*)o);
        return (outb - buf);

        break;
    case 32:
        outb += lmcp_pack_NavigationAction_header(outb, (NavigationAction*)o);
        outb += lmcp_pack_NavigationAction(outb, (NavigationAction*)o);
        return (outb - buf);

        break;
    case 33:
        outb += lmcp_pack_LoiterAction_header(outb, (LoiterAction*)o);
        outb += lmcp_pack_LoiterAction(outb, (LoiterAction*)o);
        return (outb - buf);

        break;
    case 34:
        outb += lmcp_pack_LoiterTask_header(outb, (LoiterTask*)o);
        outb += lmcp_pack_LoiterTask(outb, (LoiterTask*)o);
        return (outb - buf);

        break;
    case 35:
        outb += lmcp_pack_Waypoint_header(outb, (Waypoint*)o);
        outb += lmcp_pack_Waypoint(outb, (Waypoint*)o);
        return (outb - buf);

        break;
    case 36:
        outb += lmcp_pack_MissionCommand_header(outb, (MissionCommand*)o);
        outb += lmcp_pack_MissionCommand(outb, (MissionCommand*)o);
        return (outb - buf);

        break;
    case 37:
        outb += lmcp_pack_MustFlyTask_header(outb, (MustFlyTask*)o);
        outb += lmcp_pack_MustFlyTask(outb, (MustFlyTask*)o);
        return (outb - buf);

        break;
    case 38:
        outb += lmcp_pack_OperatorSignal_header(outb, (OperatorSignal*)o);
        outb += lmcp_pack_OperatorSignal(outb, (OperatorSignal*)o);
        return (outb - buf);

        break;
    case 39:
        outb += lmcp_pack_OperatingRegion_header(outb, (OperatingRegion*)o);
        outb += lmcp_pack_OperatingRegion(outb, (OperatingRegion*)o);
        return (outb - buf);

        break;
    case 40:
        outb += lmcp_pack_AutomationRequest_header(outb, (AutomationRequest*)o);
        outb += lmcp_pack_AutomationRequest(outb, (AutomationRequest*)o);
        return (outb - buf);

        break;
    case 41:
        outb += lmcp_pack_PointSearchTask_header(outb, (PointSearchTask*)o);
        outb += lmcp_pack_PointSearchTask(outb, (PointSearchTask*)o);
        return (outb - buf);

        break;
    case 42:
        outb += lmcp_pack_Polygon_header(outb, (Polygon*)o);
        outb += lmcp_pack_Polygon(outb, (Polygon*)o);
        return (outb - buf);

        break;
    case 43:
        outb += lmcp_pack_Rectangle_header(outb, (Rectangle*)o);
        outb += lmcp_pack_Rectangle(outb, (Rectangle*)o);
        return (outb - buf);

        break;
    case 44:
        outb += lmcp_pack_RemoveTasks_header(outb, (RemoveTasks*)o);
        outb += lmcp_pack_RemoveTasks(outb, (RemoveTasks*)o);
        return (outb - buf);

        break;
    case 45:
        outb += lmcp_pack_ServiceStatus_header(outb, (ServiceStatus*)o);
        outb += lmcp_pack_ServiceStatus(outb, (ServiceStatus*)o);
        return (outb - buf);

        break;
    case 46:
        outb += lmcp_pack_SessionStatus_header(outb, (SessionStatus*)o);
        outb += lmcp_pack_SessionStatus(outb, (SessionStatus*)o);
        return (outb - buf);

        break;
    case 47:
        outb += lmcp_pack_VehicleActionCommand_header(outb, (VehicleActionCommand*)o);
        outb += lmcp_pack_VehicleActionCommand(outb, (VehicleActionCommand*)o);
        return (outb - buf);

        break;
    case 48:
        outb += lmcp_pack_VideoStreamAction_header(outb, (VideoStreamAction*)o);
        outb += lmcp_pack_VideoStreamAction(outb, (VideoStreamAction*)o);
        return (outb - buf);

        break;
    case 49:
        outb += lmcp_pack_VideoStreamConfiguration_header(outb, (VideoStreamConfiguration*)o);
        outb += lmcp_pack_VideoStreamConfiguration(outb, (VideoStreamConfiguration*)o);
        return (outb - buf);

        break;
    case 50:
        outb += lmcp_pack_VideoStreamState_header(outb, (VideoStreamState*)o);
        outb += lmcp_pack_VideoStreamState(outb, (VideoStreamState*)o);
        return (outb - buf);

        break;
    case 51:
        outb += lmcp_pack_AutomationResponse_header(outb, (AutomationResponse*)o);
        outb += lmcp_pack_AutomationResponse(outb, (AutomationResponse*)o);
        return (outb - buf);

        break;
    case 52:
        outb += lmcp_pack_RemoveZones_header(outb, (RemoveZones*)o);
        outb += lmcp_pack_RemoveZones(outb, (RemoveZones*)o);
        return (outb - buf);

        break;
    case 53:
        outb += lmcp_pack_RemoveEntities_header(outb, (RemoveEntities*)o);
        outb += lmcp_pack_RemoveEntities(outb, (RemoveEntities*)o);
        return (outb - buf);

        break;
    case 54:
        outb += lmcp_pack_FlightDirectorAction_header(outb, (FlightDirectorAction*)o);
        outb += lmcp_pack_FlightDirectorAction(outb, (FlightDirectorAction*)o);
        return (outb - buf);

        break;
    case 55:
        outb += lmcp_pack_WeatherReport_header(outb, (WeatherReport*)o);
        outb += lmcp_pack_WeatherReport(outb, (WeatherReport*)o);
        return (outb - buf);

        break;
    case 56:
        outb += lmcp_pack_FollowPathCommand_header(outb, (FollowPathCommand*)o);
        outb += lmcp_pack_FollowPathCommand(outb, (FollowPathCommand*)o);
        return (outb - buf);

        break;
    case 57:
        outb += lmcp_pack_PathWaypoint_header(outb, (PathWaypoint*)o);
        outb += lmcp_pack_PathWaypoint(outb, (PathWaypoint*)o);
        return (outb - buf);

        break;
    case 58:
        outb += lmcp_pack_StopMovementAction_header(outb, (StopMovementAction*)o);
        outb += lmcp_pack_StopMovementAction(outb, (StopMovementAction*)o);
        return (outb - buf);

        break;
    case 59:
        outb += lmcp_pack_WaypointTransfer_header(outb, (WaypointTransfer*)o);
        outb += lmcp_pack_WaypointTransfer(outb, (WaypointTransfer*)o);
        return (outb - buf);

        break;
    case 60:
        outb += lmcp_pack_PayloadStowAction_header(outb, (PayloadStowAction*)o);
        outb += lmcp_pack_PayloadStowAction(outb, (PayloadStowAction*)o);
        return (outb - buf);

        break;
    default:
        return 0;
    }
}
