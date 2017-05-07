// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "Dpss.h"
#include "DRand.h"
#include <iostream>
#include <fstream>
//#include <direct.h> //_mkdir

using namespace std;

double Dpss::DistanceToCurrentSegment(VehicleTelemetry& uav)
{
    xyPoint p;
    Segment q;
    if(CurrentSegmentAndXYPosition(uav,p,q) < 0)
        return 0.0;
    return q.distToClosestPoint(p);
}

double Dpss::AngleToCurrentSegment(VehicleTelemetry& uav)
{
    xyPoint p;
    Segment q;
    if(CurrentSegmentAndXYPosition(uav,p,q) < 0)
        return 0.0;

    double angleDiff = ((dPi/2.0 - uav.headingInRadians) - q.angle()) - dPi;
    while(angleDiff > dPi)
        angleDiff -= 2*dPi;
    while(angleDiff < -dPi)
        angleDiff += 2*dPi;

    return angleDiff;
}

int Dpss::CurrentSegmentAndXYPosition(VehicleTelemetry& uav, xyPoint& xyPos, Segment& currentSegment)
{
    int toWp = -1;
    int len = (int) m_TrueWaypoints.size();

    // translate aircraft position to xyz plane of waypoint stored plan
    m_FlatEarthConverter.ConvertLatLong_radToNorthEast_m(uav.latitudeInRadians, uav.longitudeInRadians, xyPos.y, xyPos.x);
    xyPos.z = uav.altitudeInMeters;

    currentSegment.a = xyPos;
    currentSegment.b = xyPos;

    if(len != (int) m_WpIDList.size() || len != (int) m_RdIDList.size() || m_TrueWaypoints.empty() || m_TrueRoad.empty())
        return -1; // error

    // decode VSCS waypoint numbers to stored waypoint indices
    for(int k=0; k<len; k++)
        if(m_WpIDList[k] == ((int) uav.toWaypointNumber))
            toWp = k;

    // check for heading toward lost comm point
    if(uav.toWaypointNumber == m_LostCommWaypointNumber)
        toWp = m_LostCommRedirectNumber;

    // if couldn't find "To" wp, return error
    if(toWp == -1)
        return -1; // error

    // need to find segment for proper mapping, check previous and current first
    Segment q1(m_TrueWaypoints[(toWp<2)?(len-2+toWp):(toWp-2)],m_TrueWaypoints[(toWp==0)?(len-1):(toWp-1)]);
    Segment q2(m_TrueWaypoints[(toWp==0)?(len-1):(toWp-1)],m_TrueWaypoints[toWp]);

    if(q1.distToClosestPoint(xyPos) < (q2.distToClosestPoint(xyPos)-70.0))
    {
        toWp--;
        if(toWp < 0) toWp = len-1;
    }

    currentSegment.a = m_TrueWaypoints[toWp];
    currentSegment.b = m_TrueWaypoints[(toWp==0)?(len-1):(toWp-1)];

    return toWp; // no error
}

void Dpss::PreProcessPath(DpssWaypoint pathPoints[], int numPoints, std::vector<xyPoint>& xyPathPoints)
{
    xyPathPoints.clear();
    if( pathPoints == NULL ) return;
    if( numPoints <= 0 ) return;

    UpdateLinearization(pathPoints, numPoints);
    m_FlatEarthConverter.ConvertLatLong_radToNorthEast_m(m_LostCommPointLatitudeInRadians, m_LostCommPointLongitudeInRadians, m_LostCommPoint.y, m_LostCommPoint.x);

    // translate lat/lon to x-y plane
    for(int k=0; k<numPoints; k++)
    {
        xyPoint pt;
        m_FlatEarthConverter.ConvertLatLong_radToNorthEast_m(pathPoints[k].latitudeInRadians, pathPoints[k].longitudeInRadians, pt.y, pt.x);
        pt.z = pathPoints[k].altitudeInMeters;
        xyPathPoints.push_back(pt);
    }

    // make sure we don't step out of bounds on interators
    if(xyPathPoints.size() < 2)
    {
        m_PlanningRoad.assign(xyPathPoints.begin(), xyPathPoints.end());
        return;
    }

    // remove extraneous points from list
    //  - corresponds to angles of less than 1/10 degree or
    //  - segment lengths less than 1 meter
    vector<xyPoint>::iterator a = xyPathPoints.begin();
    vector<xyPoint>::iterator b = xyPathPoints.begin() + 1;
    vector<xyPoint>::iterator c = xyPathPoints.begin() + 2;
    double beta, seperation;
    while( (b != xyPathPoints.end()) && (c != xyPathPoints.end()) )
    {
        seperation = ComputeSeperation(beta, *a, *b, *c);
        if(fabs(beta) < dDeg2Rad*0.1 && seperation < 1)
        {
            b = xyPathPoints.erase(b);
            c = b+1;
        }
        else { a++; b++; c++; }
    }

    //RemoveRoadPointsOutOfCommRange(xyPathPoints);

    m_PlanningRoad.assign(xyPathPoints.begin(), xyPathPoints.end());
}

void Dpss::PreProcessPath(std::vector<xyPoint>& xyPathPoints)
{
    if( xyPathPoints.empty() ) return;

    // make sure we don't step out of bounds on interators
    if(xyPathPoints.size() < 2)
    {
        m_PlanningRoad.assign(xyPathPoints.begin(), xyPathPoints.end());
        return;
    }

    // remove extraneous points from list
    //  - corresponds to angles of less than 1/10 degree or
    //  - segment lengths less than 1 meter
    vector<xyPoint>::iterator a = xyPathPoints.begin();
    vector<xyPoint>::iterator b = xyPathPoints.begin() + 1;
    vector<xyPoint>::iterator c = xyPathPoints.begin() + 2;
    double beta, seperation;
    while( (b != xyPathPoints.end()) && (c != xyPathPoints.end()) )
    {
        seperation = ComputeSeperation(beta, *a, *b, *c);
        if(fabs(beta) < dDeg2Rad*0.1 && seperation < 1)
        {
            b = xyPathPoints.erase(b);
            c = b+1;
        }
        else { a++; b++; c++; }
    }

    //RemoveRoadPointsOutOfCommRange(xyPathPoints);

    m_PlanningRoad.assign(xyPathPoints.begin(), xyPathPoints.end());
}

void Dpss::PostProcessPlan(std::vector<xyPoint>& plan, double threshold)
{
    if(plan.size() < 3) return;

    // remove points that are too close (within threshold distance)
    // with the exception of station points and endpoints
    int N = (int) plan.size();
    Dpss_Data_n::xyPoint::PointAttributes originalStartAttributes = plan[0].attributes;
    Dpss_Data_n::xyPoint::PointAttributes originalEndAttributes = plan[N-1].attributes;
    plan[0].attributes = Dpss_Data_n::xyPoint::Station;
    plan[N-1].attributes = Dpss_Data_n::xyPoint::Station;

    bool planModified = false;
    do
    {
        planModified = false;
        vector<xyPoint>::iterator a = plan.begin();
        vector<xyPoint>::iterator b = plan.begin() + 1;
        while( (a != plan.end()) && (b != plan.end()) )
        {
            if(a->dist(*b) < threshold)
            {
                if(a->attributes != Dpss_Data_n::xyPoint::None &&
                   b->attributes != Dpss_Data_n::xyPoint::None)
                {
                    a++;
                    b++;
                    continue;
                }

                if(a->attributes != Dpss_Data_n::xyPoint::None &&
                   b->attributes == Dpss_Data_n::xyPoint::None)
                {
                    b = plan.erase(b);
                    planModified = true;
                    continue;
                }

                if(a->attributes == Dpss_Data_n::xyPoint::None &&
                   b->attributes != Dpss_Data_n::xyPoint::None)
                {
                    a = plan.erase(a);
                    b = a+1;
                    planModified = true;
                    continue;
                }

                // TODO: don't take average - pick best
                a->x = (a->x + b->x)/2.0;
                a->y = (a->y + b->y)/2.0;
                a->z = (a->z + b->z)/2.0;
                b = plan.erase(b);
                planModified = true;
            }
            else
            {
                a++;
                b++;
            }
        }
    } while(planModified);

    plan[0].attributes = originalStartAttributes;
    plan[( (int)plan.size() ) - 1].attributes = originalEndAttributes;
}

void Dpss::RemoveRoadPointsOutOfCommRange(std::vector<xyPoint>& xyPathPoints)
{
    // make sure we don't step out of bounds on interators
    if(xyPathPoints.size() < 2)
        return;

    // remove points that are out of comm range in 2 phases:
    //  (1) add points at intersections with max comm range
    //  (2) remove all points out of comm range
    xyPoint lostComm;
    m_FlatEarthConverter.ConvertLatLong_radToNorthEast_m(m_LostCommPointLatitudeInRadians, m_LostCommPointLongitudeInRadians, lostComm.y, lostComm.x);

    // add points at intersections
    vector<xyPoint>::iterator a = xyPathPoints.begin();
    vector<xyPoint>::iterator b = xyPathPoints.begin() + 1;
    int aIndex = 0;
    while( (a != xyPathPoints.end()) && (b != xyPathPoints.end()) )
    {
        if( (lostComm.dist(*a) > m_MaxCommunicationRange && lostComm.dist(*b) < m_MaxCommunicationRange) ||
            (lostComm.dist(*b) > m_MaxCommunicationRange && lostComm.dist(*a) < m_MaxCommunicationRange) )
        {
            // find intersection point and insert to path
            // Reference to point 'a'
            xyPoint pathSegmentEnd = (*b) - (*a);
            xyPoint circleCenter = lostComm - (*a);

            // rotate to horizontal to do all calculations
            double th = atan2(pathSegmentEnd.y, pathSegmentEnd.x);
            pathSegmentEnd.Rotate( -th );
            circleCenter.Rotate( -th );

            // compute interesection with comm range disc, solutions only exist when in certain range
            if( fabs(circleCenter.y) <= m_MaxCommunicationRange )
            {
                // two possible solutions
                double intersectionA, intersectionB;
                intersectionA = circleCenter.x + sqrt( m_MaxCommunicationRange*m_MaxCommunicationRange -  circleCenter.y*circleCenter.y );
                intersectionB = circleCenter.x - sqrt( m_MaxCommunicationRange*m_MaxCommunicationRange -  circleCenter.y*circleCenter.y );

                // rotated such that intersection should be between 0 and pathSegmentEnd.x, note pathSegmentEnd.x > 0
                // it should be impossible for two intersections to take place since one point is inside disc and other is outside
                xyPoint intersectionPoint;
                if(intersectionA >= 0.0 && intersectionA <= pathSegmentEnd.x)
                {
                    double percentAlong = intersectionA/pathSegmentEnd.x;
                    intersectionPoint = (*a)*(1.0-percentAlong) + (*b)*percentAlong;
                    xyPathPoints.insert(b,intersectionPoint);
                    aIndex++;
                    a = xyPathPoints.begin() + aIndex;
                    b = xyPathPoints.begin() + aIndex + 1;
                }
                else if(intersectionB >= 0.0 && intersectionB <= pathSegmentEnd.x)
                {
                    double percentAlong = intersectionB/pathSegmentEnd.x;
                    intersectionPoint = (*a)*(1.0-percentAlong) + (*b)*percentAlong;
                    xyPathPoints.insert(b,intersectionPoint);
                    aIndex++;
                    a = xyPathPoints.begin() + aIndex;
                    b = xyPathPoints.begin() + aIndex + 1;
                }
            }
        }

        a++;
        b++;
        aIndex++;
    }

    // deletes points that lie entirely out of comm range
    a = xyPathPoints.begin();
    while( a != xyPathPoints.end() )
    {
        if( lostComm.dist(*a) > (m_MaxCommunicationRange+1.0) )
            a = xyPathPoints.erase(a);
        else 
            a++;
    }
}

void Dpss::SetSingleDirectionPlanning(bool val)
{
    m_SingleDirectionPlan = val;
}

bool Dpss::GetSingleDirectionPlanning()
{
    return m_SingleDirectionPlan;
}

double Dpss::CandidateCost(std::vector<double>& x)
{
    double cost = 0.0;

    switch(m_SelectedOptimization)
    {
    case Dpss::Path:
        cost = PlanCost(x);
        break;

    case Dpss::SensorPointingForward:
        cost = SensorPointingCostForward(x);
        break;

    case Dpss::SensorPointingReverse:
        cost = SensorPointingCostReverse(x);
        break;

    default:
        cost = 0.0;
    }

    return cost;
}

void Dpss::RemoveZeroLengthSegments(std::vector<xyPoint> &xyPoints)
{
    xyPoint a;
    if(xyPoints.size() < 2) return;

    // remove zero length segments from list
    vector<xyPoint>::iterator q = xyPoints.begin();
    vector<xyPoint>::iterator r = xyPoints.begin() + 1;
    while( (q != xyPoints.end()) && (r != xyPoints.end()) )
    {
        a.x = r->x - q->y;
        a.y = r->y - q->y;
        if(a.len() < 1e-10)
            r = xyPoints.erase(r);
        else { q++; r++; }
    }
}

void Dpss::UpdateLinearization(DpssWaypoint points[], int numPoints)
{
    // handle nonsense input
    if( points == NULL ) return;
    if( numPoints <= 0 ) return;

    //convert to x-y by picking midpoint all lat/lon in list
    DpssWaypoint maxLatLon;
    maxLatLon.latitudeInRadians = points[0].latitudeInRadians;
    maxLatLon.longitudeInRadians = points[0].longitudeInRadians;
    
    DpssWaypoint minLatLon;
    minLatLon.latitudeInRadians = points[0].latitudeInRadians;
    minLatLon.longitudeInRadians = points[0].longitudeInRadians;

    // find max and min latitudes and longitudes
    for(int k=1; k<numPoints; k++)
    {
        if(points[k].latitudeInRadians > maxLatLon.latitudeInRadians)
            maxLatLon.latitudeInRadians = points[k].latitudeInRadians;
        if(points[k].longitudeInRadians > maxLatLon.longitudeInRadians)
            maxLatLon.longitudeInRadians = points[k].longitudeInRadians;
        if(points[k].latitudeInRadians < minLatLon.latitudeInRadians)
            minLatLon.latitudeInRadians = points[k].latitudeInRadians;
        if(points[k].longitudeInRadians < minLatLon.longitudeInRadians)
            minLatLon.longitudeInRadians = points[k].longitudeInRadians;
    }

    // compute average lat/lon
    DpssWaypoint aveLatLon;
    aveLatLon.latitudeInRadians  = 0.5*(maxLatLon.latitudeInRadians  + minLatLon.latitudeInRadians);
    aveLatLon.longitudeInRadians = 0.5*(maxLatLon.longitudeInRadians + minLatLon.longitudeInRadians);

    m_FlatEarthConverter.Initialize(aveLatLon.latitudeInRadians, aveLatLon.longitudeInRadians);
}

double Dpss::ComputeSeperation(double& beta, xyPoint& a, xyPoint& b, xyPoint& c)
{
    xyPoint q1,q2,q3;
    double q1len, q2len, q3len, seperation, triangleArea;

    // normalize, remove if necessary
    q1.x = b.x - a.x;
    q1.y = b.y - a.y;
    q1len = sqrt(q1.x*q1.x + q1.y*q1.y);
    if( q1len < 1e-6 )
    {
        beta = 0.0;
        return 0.0;
    }

    q2.x = c.x - b.x;
    q2.y = c.y - b.y;
    q2len = sqrt(q2.x*q2.x + q2.y*q2.y);
    if( q2len < 1e-6 )
    {
        beta = 0.0;
        return 0.0;
    }

    // calculate angle from straight
    //innerProduct = (q1.x*q2.x + q1.y*q2.y)/(q1len*q2len);
    //if(innerProduct >  1.0) innerProduct =  1.0;
    //if(innerProduct < -1.0) innerProduct = -1.0;
    //beta = acos(innerProduct);

    beta = atan2(q1.y,q1.x) - atan2(q2.y,q2.x);
    if(beta < -dPi)
        beta += 2*dPi;
    if(beta > dPi)
        beta -= 2*dPi;
    
    // calculate affected area
    q3.x = c.x - a.x;
    q3.y = c.y - a.y;
    q3len = sqrt(q3.x*q3.x + q3.y*q3.y);
    if(q3len < 1e-6)
        seperation = q1len;
    else
        seperation = fabs(q1.x*q3.y - q3.x*q1.y)/q3len;
    triangleArea = 0.5*seperation*q3len;

    return seperation;
}

void Dpss::PrintRoadXY(char fileName[], std::vector<xyPoint> &road)
{
#ifdef TODO
  char realFileName[512];
  sprintf_s(realFileName, "%s%s",m_OutputPath.c_str(), fileName);
    ofstream out(realFileName);
    if( !out )
        return;

    out << "sroad = [";
    for(int i=0; i<(int)road.size(); i++)
    {
        out << "[" << road[i].x << ", " << road[i].y << "]; ..." << endl;
    }
    out << "];" << endl;

    out.close();
#endif
}

void Dpss::PrintRoadXYZ(char fileName[], std::vector<xyPoint> &road)
{
#ifdef TODO
  char realFileName[512];
  sprintf_s(realFileName, "%s%s",m_OutputPath.c_str(), fileName);
    ofstream out(realFileName);
    if( !out )
        return;

    out << "sroad = [";
    for(int i=0; i<(int)road.size(); i++)
    {
        out << "[" << road[i].x << ", " << road[i].y << ", " << road[i].z << "]; ..." << endl;
    }
    out << "];" << endl;

    out.close();
#endif
}

void Dpss::PrintRoadLatLon(char fileName[], DpssWaypoint* wp, int numWps)
{
#ifdef TODO
  char realFileName[512];
  sprintf_s(realFileName, "%s%s",m_OutputPath.c_str(), fileName);
    ofstream out(realFileName);
    if( !out )
        return;

    out << "sroad = [";
    for(int i=0; i<numWps; i++)
    {
        out << "[" << wp[i].latitudeInRadians << ", " << wp[i].longitudeInRadians << "]; ..." << endl;
    }
    out << "];" << endl;

    out.close();
#endif
}

void Dpss::FullDebugPlan()
{
#ifdef TODO
    struct tm newtime;
    __time64_t long_time;
    errno_t err;

    // Get time as 64-bit integer.
    _time64( &long_time ); 

    // Convert to local time.
    err = _localtime64_s( &newtime, &long_time ); 
    if(err)
        return;

    char fileName[512];
    sprintf_s(fileName, "%sdpss\\",m_OutputPath.c_str());

    // try to create intermediate directory
    _mkdir(fileName);
    
    // now make the full path + file name
    sprintf_s(fileName, "%sdpss\\dpss_%dptPlan_%d%d%d.m",m_OutputPath.c_str(), m_TrueWaypoints.size(), newtime.tm_hour, newtime.tm_min, newtime.tm_sec);

    // make sure it's a unique file name
    bool goodFile = false;
    FILE* file;
    int counter = 0;
    while(!goodFile && counter < 10)
    {
        // check to see if it exists already
        if(!fopen_s(&file, fileName, "r") )
        {
            fclose(file);
            sprintf_s(fileName, "%sdpss\\dpss_%dptPlan_%d%d%d_%d.m",m_OutputPath.c_str(), m_TrueWaypoints.size(), newtime.tm_hour, newtime.tm_min, newtime.tm_sec, (int) (randu()*1000) );
            counter++;
        }
        else
            goodFile = true;
    }

    ofstream out(fileName);
    if( !out )
        return;

    out << "idlist = [";
    for(int i=0; i<(int)m_RdIDList.size(); i++)
    {
        out << "[" << m_RdIDList[i] << "]; ..." << endl;
    }
    out << "];" << endl;

    out << "road = [";
    for(int i=0; i<(int)m_TrueRoad.size(); i++)
    {
        out << "[" << m_TrueRoad[i].x << ", " << m_TrueRoad[i].y << "]; ..." << endl;
    }
    out << "];" << endl;

    out << "waypoints = [";
    for(int i=0; i<(int)m_TrueWaypoints.size(); i++)
    {
        out << "[" << m_TrueWaypoints[i].x << ", " << m_TrueWaypoints[i].y << "]; ..." << endl;
    }
    out << "];" << endl;

    // build matlab plotting
    out << "figure(1); clf;" << endl;
    out << "plot(road(:,1),road(:,2),'b-','LineWidth',3); hold on;" << endl;
    out << "plot(road(:,1),road(:,2),'b.');" << endl;
    out << "plot(waypoints(:,1),waypoints(:,2),'r-','LineWidth',2); hold on;" << endl;
    out << "plot(waypoints(:,1),waypoints(:,2),'ro','MarkerSize',6,'LineWidth',2);" << endl;
    out << "for n=1:length(waypoints(:,1))," << endl;
    out << "   plot([waypoints(n,1) road(idlist(n)+1,1)],[waypoints(n,2) road(idlist(n)+1,2)],'k','LineWidth',2);" << endl;
    out << "end;" << endl;
    out << "axis equal;"<< endl;
    out << "axis off;"<< endl;

    out.close();
#endif
}