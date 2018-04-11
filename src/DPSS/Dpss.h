// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#pragma once
#include "DpssDefs.h"
#include "DpssDataTypes.h"
#include "ObjectiveParameters.h"
#include "SmoothPathInput.h"
#include "DpssWaypoint.h"
#include "VehicleGoToPoint.h"
#include "VehicleTelemetry.h"
#include "VehiclePoint.h"
#include "UnitConversions.h"
#include <string>
#include <vector>
#include <time.h>

class Dpss
{
public:
  //standard creator
  Dpss();

  //standard destructor
  ~Dpss();

  //  The function for smoothing the path definition into a flyable plan
  //
  //  Parameters:
  //  pathPoints      - These are the points for the path definition (INPUT parameter only)
  //  numPoints       - The number of points in pathPoints (INPUT parameter only)
  //  spi             - This structure contains the parameters for the actual path smoothing (INPUT parameter only)
  //  outputPoints    - This will contain the smoothed path result of the function. This is an array variable and will
  //                    be pre-allocated with a set number of elements. The number of elements contained in the array
  //                    will be passed in through the numOutputPoints variable. Due to memory issues, this variable must 
  //                    be used as is and not reallocated. Once you have populated this array with your elements set the
  //                    numOutputPoints variable to the new number of points to be used. (INPUT and OUTPUT parameter)
  //  numOutputPoints - This will be used to pass in the capacity of the the outputPoints array and to return the number
  //                    of points smoothed points. This variable is a pointer and must not be reallocated. (INPUT and 
  //                    OUTPUT parameter)    
  void SmoothPath(DpssWaypoint pathPoints[], int numPoints, 
                  SmoothPathInput* spi, DpssWaypoint* outputPoints, int* numOutputPoints);
    
  //  Updates the points that the vehicles will fly
  //
  //  Parameters:
  //  planPoints  - An array containing the new waypoints to fly (INPUT parameter only)
  //  numPoints   - The number of points in the planPoints array (INPUT parameter only)
  void SetObjective(DpssWaypoint pathPoints[], int numPathPoints, DpssWaypoint planPoints[], int numPlanPoints, ObjectiveParameters* op);

  // overloaded function to allow for direct xy access
  void SetObjective(std::vector<xyPoint>& path, std::vector<xyPoint>& plan,    ObjectiveParameters* op);

  //  Adds the vehicles specified in the vehicleIds array to the system.
  //
  //  Parameters:
  //  vehicleIds  - Array containing the numeric vehicle IDs of the vehicles
  //                to be added to the system (INPUT paramter only)
  //  numVehicles - The number of vehicle Ids in the vehicleIds array (INPUT
  //                parameter only)
  //  Returns:
  //  The new value for the number of vehicles in the system. Used as 
  //  a confirmation that the function secceeded
  int AddVehicles(int vehicleIds[], int numVehicles);

  //  Removes the vehicles specified in the vehicleIds array from the system.
  //
  //  Parameters:
  //  vehicleIds  - Array containing the numeric vehicle IDs of the vehicles
  //                to be removed from the system (INPUT paramter only)
  //  numVehicles - The number of vehicle Ids in the vehicleIds array (INPUT
  //                parameter only)
  //  Returns:
  //  The new value for the number of vehicles in the system. Used as 
  //  a confirmation that the function secceeded
  int RemoveVehicles(int vehicleIds[], int numVehicles);

  //  Updates the position of a vehicle
  //
  //  Paremeters:
  //  telemetry - Structure containing vehicle information (INPUT parameter only)
  void UpdateVehicleTelemetry(VehicleTelemetry telemetry);

  // Updates the Dpss using the most recent information
  //
  //  Parameters:
  //  sensorPoints          - Array that will contain the new stare points for the vehicles for the current cycle.
  //                          This array is pre-allocated and must not be re-allocated. (OUTPUT parameter only)
  //  numSensorPoints       - This array passes in the number of elements in the sensorPoints array and will be 
  //                          used to return the number of sensorPoints in this update. Set to value representing 
  //                          the number of sensorPoints for this update. (INPUT and OUTPUT parameter)
  //  vehicleGotoPoints     - Array that will contain the new vehicle go to points for the vehicles for the 
  //                          current cycle. This array is pre-allocated and must not be re-allocated. (OUTPUT 
  //                          parameter only)
  //  numGotoPoints         - This array passes in the number of elements in the vehicleGotoPoints array and will be 
  //                          used to return the number of vehicleGotoPoints in this update. Set to value representing 
  //                          the number of vehicleGotoPoints for this update. (INPUT and OUTPUT parameter)
  //  turnPoints            - Array that will contain the points at which the vehicles will turn around the current cycle.
  //                          This array is pre-allocated and must not be re-allocated. (OUTPUT parameter only)
  //  numTurnPoints         - This array passes in the number of elements in the turnPoints array and will be 
  //                          used to return the number of turnPoints in this update. Set to value representing 
  //                          the number of turnPoints for this update. (INPUT and OUTPUT parameter)
  //  dpssState             - Structure for describing the state of the DPSS. Flags in the structure should be set
  //                          when the corresponding information is changed. (INPUT and OUTPUT parameter)
  void UpdateDpss(VehiclePoint sensorPoints[], int* numSensorPoints, 
                  VehicleGoToPoint vehicleGoToPoints[], int* numGotoPoints, 
                  VehiclePoint turnPoints[], int* numTurnPoints);

  void SetLostCommWaypointNumber(unsigned short lostCommWaypointNumber);
  void SetOutputPath(const char* path);

  // cost function to allow outside optimization classes to pointing cost for road/wp configuration
  double CandidateCost(std::vector<double>& x);

  
  // take optimized central plan and offset for look angle
  void OffsetPlanForward(std::vector<xyPoint> &xyPlanPoints, std::vector<xyPoint> &forwardPlan);
  void OffsetPlanReverse(std::vector<xyPoint> &xyPlanPoints, std::vector<xyPoint> &reversePlan);

  // builds x,y road from lat/lon coordinates and removes nonsense segments
  void PreProcessPath(DpssWaypoint pathPoints[], int numPoints, std::vector<xyPoint>& xyPathPoints);
  void PreProcessPath(std::vector<xyPoint>& xyPathPoints);

  // greedy method for selecting center waypoints from a given road input
  void PlanQuickly(std::vector<xyPoint> &xyPoints, int maxWps);

#ifdef AFRL_INTERNAL_ENABLED
  // accurate method for selecting center waypoints from a given road input
  //void PlanPrecisely(std::vector<xyPoint> &xyPoints, int maxWps);
#endif

  // removes road points that lie outside of comm range
  void RemoveRoadPointsOutOfCommRange(std::vector<xyPoint>& xyPathPoints);

  // cuts waypoints that are within 'threshold' distance of other waypoints
  // basically, declutters the plan
  void PostProcessPlan(std::vector<xyPoint>& plan, double threshold);

  // alerts the algorithm that the path is circular not linear
  void SetSingleDirectionPlanning(bool val);

  // returns the current understanding of circular or linear planning
  bool GetSingleDirectionPlanning();

  // helper function to break large road task into smaller sub-tasks
  void RoadPosToWpSegments(xyPoint roadPt, xyPoint& forwardPt, xyPoint& reversePt, int& forwardIndexA, int& forwardIndexB, int& reverseIndexA, int& reverseIndexB);

  // uses mapping to steer camera
  void CalculateStarePoint(VehiclePoint &starePoint, VehicleTelemetry &vehiclePosition);

  // overloaded for xypoints, forces global search
  void CalculateStarePoint(xyPoint &starePoint, xyPoint &vehiclePosition);

  void SetNominalAzimuth_rad(double& dNominalAzimuth_rad)
  {
    m_NominalAzimuth = dNominalAzimuth_rad;
  }
  void SetNominalElevation_rad(double& dNominalElevation_rad)
  {
    m_NominalElevation = fabs(dNominalElevation_rad);
  }
  void SetNominalAltitude_m(double& dNominalAltitude_m)
  {
    m_NominalAltitudeInMeters = dNominalAltitude_m;
  }

private:
    
    // set lat/lon position for center of linearization
    void UpdateLinearization(DpssWaypoint points[], int numPoints);

    // removes redundant points from a list - guarantees no zero length segments
    void RemoveZeroLengthSegments(std::vector<xyPoint> &xyPoints);

    // build full plan from forward and reverse plans and format in lat/lon
    void CombinePlans(std::vector<xyPoint> &forwardPlan, std::vector<xyPoint> &reversePlan, DpssWaypoint* outputPoints, int* numOutputPoints);

    // assumes uniform speed camera motion and generates stare points for all waypoints
    void CorrespondingStarePoints(std::vector<xyPoint>& plan, std::vector<xyPoint>& road, std::vector<xyPoint>& starePoints);

    // cuts waypoints that cause stare point crossing
    void CleanUpStareAngles(std::vector<xyPoint>& plan, std::vector<xyPoint>& road);

    // Sets up optimization class to find center waypoints in normalized coordinates
    double PathOptimization(std::vector<double>& x);

    // Cost for normalized coordinate solution
    double PlanCost(std::vector<double>& x);

    // calculates distance from the currently commanded segment
    double DistanceToCurrentSegment(VehicleTelemetry& uav);

    // calculates course angle difference from currently commanded segment
    double AngleToCurrentSegment(VehicleTelemetry& uav);

    // helper function to translate from telemetry to xy plane
    int CurrentSegmentAndXYPosition(VehicleTelemetry& uav, xyPoint& xyPos, Segment& currentSegment);

    // coordinate transformations
    int UavWpToVscsWp(int uavWp);
    int VscsWpToUavWp(int vscsWp);

    int UavWpToStandardWp(int uavWp);
    int StandardWpToUavWp(int standardWp);
    
    int RoadIndexToClosestStandardWp(int roadIndex, int direction);
    int StandardWpToRoadIndex(int standardWp);
    
    double RoadIndexToNormalizedRoadPos(int roadIndex);
    int NormalizedRoadPosToClosestRoadIndex(double normalizedRoadPos);

    double NormalizedRoadPosToVehiclePos(xyPoint& p, double normalizedRoadPos, int direction);
    double VehiclePosToNormalizedRoadPos(xyPoint& vehiclePos);
    
    void RoadIndexToVehiclePos(xyPoint& p, int roadIndex, int direction);
    int VehiclePosToRoadIndex(xyPoint& vehiclePos);

    // specialized coordinate transformations
    int NormalizedRoadPosToXyRoadPos(xyPoint& p, double x);
    double CorrespondingNormalizedRoadLocation(VehicleTelemetry &pos);
public:    //RAS
    unsigned short NormalizedRoadPosToVscsWp(double roadPos, int direction);
    double CorrespondingNormalizedRoadLocation(xyPoint &pos);
private:    //RAS

    // Central method to whole operation
    // computes how wps are mapped to road points for sensor steering
    void CalculateWpToRdIndexMap();
    void BuildConversionMappings(std::vector<double>& forwardSolution, std::vector<double>& reverseSolution);

    // methods for optimizing look angle mapping for input road and waypoints
    double SensorPointingCostForward(std::vector<double>& x);
    double SensorPointingCostReverse(std::vector<double>& x);
    double ComputeSeperation(double& beta, xyPoint& a, xyPoint& b, xyPoint& c);
    double MaxDeviation(double a, double b);
    
    // debug functions for showing results of calculations
    void PrintRoadXY(char fileName[], std::vector<xyPoint> &road);
    void PrintRoadXYZ(char fileName[], std::vector<xyPoint> &road);
    void PrintRoadLatLon(char fileName[], DpssWaypoint* wp, int numWps);
    void FullDebugPlan();
    

    /////// Parameters ///////

    // Camera angles: set in planning phase by SmoothPath
    double m_NominalAzimuth;
    double m_NominalElevation;
    double m_NominalAltitudeInMeters;

    std::string m_OutputPath;

    double m_RendezvousDistance;
    double m_ReverseManeuverDistance;
    double m_NearWpThreshold;
    unsigned short m_LostCommWaypointNumber;
    int m_LostCommRedirectNumber;
    double m_MaxCommunicationRange;

    unsigned int m_SameSidePlan;
    bool m_SingleDirectionPlan;
    bool m_TerrainFollowing;

    double m_LreLatitudeInRadians;
    double m_LreLongitudeInRadians;
    xyPoint m_LaunchRecoveryPoint;

    double m_LostCommPointLatitudeInRadians;
    double m_LostCommPointLongitudeInRadians;
    xyPoint m_LostCommPoint;


    /////// Bookkeeping:Planning ///////

    // member for converting between lat/lon and x,y
    // re-initialized whenever new inputs are available (SmoothPath, UpdateSensorPath, UpdatePlan)
    uxas::common::utilities::CUnitConversions m_FlatEarthConverter;
    
    // full input road in x,y coordinates
    // initialized in PreProcessPath
    // used by CleanUpStareAngles
    std::vector<xyPoint> m_PlanningRoad;

    // input road indices that correspond to points *not* removed in the quick planning stage
    // initialized in PlanQuickly
    // used by PlanPrecisely to form initial solution for optimization
    std::vector<int> m_QuickPlanIndices;
    
    // full input road in x,y coordinates
    // initialized in PlanPrecisely
    // used in CandidateCost to compute deviation from candidate and actual roads
    std::vector<xyPoint> m_PrecisePlanRoad;

    // mapping of input x,y road to normalized length [0...1]
    // initialized in PlanPrecisely
    // used in CandidateCost to compute deviation from candidate and actual roads
    std::vector<double> m_PrecisePlanLengths;


    /////// Bookkeeping:Operation ///////

    // actual lat/lon waypoints loaded to UAV
    std::vector<DpssWaypoint> m_LatLonWaypoints;

    // x,y coordinates of waypoints loaded to UAV
    std::vector<xyPoint> m_TrueWaypoints;

    // corresponding waypoint indices loaded to UAV
    std::vector<int> m_WpIDList;

    // actual lat/lon input road coordinates for steering
    std::vector<DpssWaypoint> m_LatLonRoad;

    // actual x,y input road coordinates for steering
    std::vector<xyPoint> m_TrueRoad;

    // normalized coordinates along input road [0...1]
    std::vector<double> m_TrueRoadLengths;

    // ?
    std::vector<int> m_RdIDList;

    // length of plan segments, used for conversions
    double m_ForwardPlanLength;
    double m_ReversePlanLength;
    double m_TrueRoadLength;
    
    // index into m_TrueWaypoints that denotes where reverse plan begins and forward plan ends
    int m_ReturnPlanWpIndex;


    /////// Bookkeeping:Vehicles ///////
    std::vector<int> m_TeamList;
    std::vector<VehicleTelemetry> m_LatLonTeamTelemetry;
    std::vector<double> m_TeamPosition;

    double m_EqualDistanceWeight;
    std::vector<double> m_ForwardStartPositions;
    std::vector<double> m_ForwardEndPositions;
    std::vector<double> m_ReverseStartPositions;
    std::vector<double> m_ReverseEndPositions;
    enum OptimizeType {
        Path,
        SensorPointingForward,
        SensorPointingReverse
    };
    OptimizeType m_SelectedOptimization;

};

//============================================

//  The following functions mirror the ones above for the DPSS class. These provide a C style calling mechanism
//  for use with dllimports and exports. Parameter descriptions are the same except for the Dpss* instance parameter.
//  This allows the C style calls to work with the DPSS class.
//
//  THESE FUNCTIONS SHOULD NOT BE MODIFIED
//

extern "C"
{
  
DPSS_API Dpss* CreateDpss();

DPSS_API void DestroyDpss(Dpss* instance);

DPSS_API void SmoothPath(Dpss* instance, 
                         DpssWaypoint pathPoints[], int numPoints, 
                         SmoothPathInput* spi,
                         DpssWaypoint* outputPoints, int* numOutputPoints);

DPSS_API void SetObjective(Dpss* instance,
                           DpssWaypoint pathPoints[], int numPathPoints,
                           DpssWaypoint planPoints[], int numPlanPoints,
                           ObjectiveParameters* op);

DPSS_API int AddVehicles(Dpss* instance, int vehicleIds[], int numVehicles);

DPSS_API int RemoveVehicles(Dpss* instance, int vehicleIds[], int numVehicles);

DPSS_API void UpdateVehicleTelemetry(Dpss* instance, VehicleTelemetry telemetry);

DPSS_API void SetOutputPath(Dpss* instance, const char* path);

DPSS_API void SetLostCommWaypointNumber(Dpss* instance, unsigned short lostCommWaypointNumber);

DPSS_API void UpdateDpss(Dpss* instance,
                         VehiclePoint sensorPoints[], int* numSensorPoints,
                         VehicleGoToPoint vehicleGotoPoints[], int* numGotoPoints, 
                         VehiclePoint turnPoints[], int* numTurnPoints);


}



