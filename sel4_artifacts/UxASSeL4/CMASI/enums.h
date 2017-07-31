#pragma once
typedef enum {
    WavelengthBand_EO = 1,
    WavelengthBand_LWIR = 2,
    WavelengthBand_AllAny = 0,
    WavelengthBand_Other = 5,
    WavelengthBand_MWIR = 4,
    WavelengthBand_SWIR = 3,
} WavelengthBand;
typedef enum {
    NavigationMode_LostComm = 5,
    NavigationMode_FlightDirector = 2,
    NavigationMode_Waypoint = 0,
    NavigationMode_Loiter = 1,
    NavigationMode_FollowLeader = 4,
    NavigationMode_TargetTrack = 3,
} NavigationMode;
typedef enum {
    FOVOperationMode_Discrete = 1,
    FOVOperationMode_Continuous = 0,
} FOVOperationMode;
typedef enum {
    GimbalPointingMode_Scan = 5,
    GimbalPointingMode_Unknown = 0,
    GimbalPointingMode_AirVehicleRelativeAngle = 1,
    GimbalPointingMode_LatLonSlaved = 3,
    GimbalPointingMode_InertialRelativeSlewRate = 4,
    GimbalPointingMode_Stowed = 6,
    GimbalPointingMode_AirVehicleRelativeSlewRate = 2,
} GimbalPointingMode;
typedef enum {
    ZoneAvoidanceType_Regulatory = 2,
    ZoneAvoidanceType_Acoustic = 3,
    ZoneAvoidanceType_Visual = 5,
    ZoneAvoidanceType_Threat = 4,
    ZoneAvoidanceType_Physical = 1,
} ZoneAvoidanceType;
typedef enum {
    LoiterType_VehicleDefault = 0,
    LoiterType_FigureEight = 3,
    LoiterType_Hover = 4,
    LoiterType_Racetrack = 2,
    LoiterType_Circular = 1,
} LoiterType;
typedef enum {
    LoiterDirection_VehicleDefault = 0,
    LoiterDirection_Clockwise = 2,
    LoiterDirection_CounterClockwise = 1,
} LoiterDirection;
typedef enum {
    ServiceStatusType_Information = 0,
    ServiceStatusType_Warning = 1,
    ServiceStatusType_Error = 2,
} ServiceStatusType;
typedef enum {
    SimulationStatusType_Paused = 2,
    SimulationStatusType_Reset = 3,
    SimulationStatusType_Running = 1,
    SimulationStatusType_Stopped = 0,
} SimulationStatusType;
typedef enum {
    SpeedType_Groundspeed = 1,
    SpeedType_Airspeed = 0,
} SpeedType;
typedef enum {
    TurnType_TurnShort = 0,
    TurnType_FlyOver = 1,
} TurnType;
typedef enum {
    CommandStatusType_Cancelled,
    CommandStatusType_Executed,
    CommandStatusType_Approved,
    CommandStatusType_Pending,
    CommandStatusType_InProcess,
} CommandStatusType;
typedef enum {
    AltitudeType_AGL,
    AltitudeType_MSL,
} AltitudeType;
typedef enum {
    TravelMode_ReverseCourse,
    TravelMode_SinglePass,
    TravelMode_Loop,
} TravelMode;
typedef enum {
    WaypointTransferMode_ReportWaypoints,
    WaypointTransferMode_AddWaypoints,
    WaypointTransferMode_RequestWaypoints,
    WaypointTransferMode_ClearWaypoints,
} WaypointTransferMode;