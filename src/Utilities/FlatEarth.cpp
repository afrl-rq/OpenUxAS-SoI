// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// FlatEarth.cpp
//
/* 
 * File:   FlatEarth.h
 * Author: Steve
 *
 * Created on March 23, 2018
 */
//////////////////////////////////////////////////////////////////////

#include "FlatEarth.h"


namespace uxas
{
namespace common
{
namespace utilities
{

void FlatEarth::Initialize(const double& latitudeInit_rad, const double& longitudeInit_rad)
{
    //no re-initialization allowed!!!!
    if (!m_isInitialized)
    {
        //assumes that the conversions will all take place within the local area of the initial latitude/longitude.
        m_latitudeInitial_rad = latitudeInit_rad;
        m_longitudeInitial_rad = longitudeInit_rad;

        double dDenominatorMeridional = std::pow((1.0 - (m_eccentricitySquared * std::pow(std::sin(latitudeInit_rad), 2.0))), (3.0 / 2.0));
        assert(dDenominatorMeridional > 0.0);
        m_radiusMeridional_m = (dDenominatorMeridional <= 0.0) ? (0.0) : (m_radiusEquatorial_m * (1.0 - m_eccentricitySquared) / dDenominatorMeridional);
        double dDenominatorTransverse = pow((1.0 - (m_eccentricitySquared * std::pow(std::sin(latitudeInit_rad), 2.0))), 0.5);
        assert(dDenominatorTransverse > 0.0);
        m_radiusTransverse_m = (dDenominatorTransverse <= 0.0) ? (0.0) : (m_radiusEquatorial_m / dDenominatorTransverse);
        m_radiusSmallCircleLatitude_m = m_radiusTransverse_m * cos(latitudeInit_rad);
        m_isInitialized = true;
    }
};

////////////////////////////////////////////////////////////////////////////
////// FROM LAT/LONG TO NORTH/EAST

void FlatEarth::ConvertLatLong_radToNorthEast_ft(const double& latitude_rad, const double& longitude_rad, double& north_ft, double& east_ft)
{
    //assumes that the conversions will all take place within the local area of the init longitude.
    if (!m_isInitialized)
    {
        Initialize(latitude_rad, longitude_rad);
    }

    double north_m = m_radiusMeridional_m * (latitude_rad - m_latitudeInitial_rad);
    double east_m = m_radiusSmallCircleLatitude_m * (longitude_rad - m_longitudeInitial_rad);

    north_ft = north_m * n_Const::c_Convert::dMetersToFeet();
    east_ft = east_m * n_Const::c_Convert::dMetersToFeet();
};

void FlatEarth::ConvertLatLong_radToNorthEast_m(const double& latitude_rad, const double& longitude_rad, double& north_m, double& east_m)
{
    //assumes that the conversions will all take place within the local area of the init longitude.
    if (!m_isInitialized)
    {
        Initialize(latitude_rad, longitude_rad);
    }

    north_m = m_radiusMeridional_m * (latitude_rad - m_latitudeInitial_rad);
    east_m = m_radiusSmallCircleLatitude_m * (longitude_rad - m_longitudeInitial_rad);
};

void FlatEarth::ConvertLatLong_degToNorthEast_m(const double& latitude_deg, const double& longitude_deg, double& north_m, double& east_m)
{
    double latitude_rad = latitude_deg * n_Const::c_Convert::dDegreesToRadians();
    double longitude_rad = longitude_deg * n_Const::c_Convert::dDegreesToRadians();

    //assumes that the conversions will all take place within the local area of the init longitude.
    if (!m_isInitialized)
    {
        Initialize(latitude_rad, longitude_rad);
    }

    north_m = m_radiusMeridional_m * (latitude_rad - m_latitudeInitial_rad);
    east_m = m_radiusSmallCircleLatitude_m * (longitude_rad - m_longitudeInitial_rad);
};

void FlatEarth::ConvertLatLong_degToNorthEast_ft(const double& latitude_deg, const double& longitude_deg, double& north_ft, double& east_ft)
{
    double latitude_rad = latitude_deg * n_Const::c_Convert::dDegreesToRadians();
    double longitude_rad = longitude_deg * n_Const::c_Convert::dDegreesToRadians();

    //assumes that the conversions will all take place within the local area of the init longitude.
    if (!m_isInitialized)
    {
        Initialize(latitude_rad, longitude_rad);
    }

    double north_m = m_radiusMeridional_m * (latitude_rad - m_latitudeInitial_rad);
    double east_m = m_radiusSmallCircleLatitude_m * (longitude_rad - m_longitudeInitial_rad);

    north_ft = north_m * n_Const::c_Convert::dMetersToFeet();
    east_ft = east_m * n_Const::c_Convert::dMetersToFeet();
};
////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////
////// FORM NORTH/EAST TO LAT/LONG

void FlatEarth::ConvertNorthEast_mToLatLong_rad(const double& north_m, const double& east_m, double& latitude_rad, double& longitude_rad)
{
    //assumes that the conversions will all take place within the local area of the init longitude.
    assert(m_radiusMeridional_m > 0.0);
    latitude_rad = (m_radiusMeridional_m <= 0.0) ? (0.0) : ((north_m / m_radiusMeridional_m) + m_latitudeInitial_rad);
    assert(m_radiusSmallCircleLatitude_m > 0.0);
    longitude_rad = (m_radiusSmallCircleLatitude_m <= 0.0) ? (0.0) : ((east_m / m_radiusSmallCircleLatitude_m) + m_longitudeInitial_rad);
};

void FlatEarth::ConvertNorthEast_mToLatLong_deg(const double& north_m, const double& east_m, double& latitude_deg, double& longitude_deg)
{
    //assumes that the conversions will all take place within the local area of the init longitude.
    assert(m_radiusMeridional_m > 0.0);
    latitude_deg = (m_radiusMeridional_m <= 0.0) ? (0.0) : ((north_m / m_radiusMeridional_m) + m_latitudeInitial_rad) * n_Const::c_Convert::dRadiansToDegrees();
    assert(m_radiusSmallCircleLatitude_m > 0.0);
    longitude_deg = (m_radiusSmallCircleLatitude_m <= 0.0) ? (0.0) : ((east_m / m_radiusSmallCircleLatitude_m) + m_longitudeInitial_rad) * n_Const::c_Convert::dRadiansToDegrees();
};

void FlatEarth::ConvertNorthEast_ftToLatLong_rad(const double& north_ft, const double& east_ft, double& latitude_rad, double& longitude_rad)
{
    double north_m = north_ft * n_Const::c_Convert::dFeetToMeters();
    double east_m = east_ft * n_Const::c_Convert::dFeetToMeters();

    //assumes that the conversions will all take place within the local area of the init longitude.
    assert(m_radiusMeridional_m > 0.0);
    latitude_rad = (m_radiusMeridional_m <= 0.0) ? (0.0) : ((north_m / m_radiusMeridional_m) + m_latitudeInitial_rad);

    assert(m_radiusSmallCircleLatitude_m > 0.0);
    longitude_rad = (m_radiusSmallCircleLatitude_m <= 0.0) ? (0.0) : ((east_m / m_radiusSmallCircleLatitude_m) + m_longitudeInitial_rad);
};

void FlatEarth::ConvertNorthEast_ftToLatLong_deg(const double& north_ft, const double& east_ft, double& latitude_deg, double& longitude_deg)
{
    double north_m = north_ft * n_Const::c_Convert::dFeetToMeters();
    double east_m = east_ft * n_Const::c_Convert::dFeetToMeters();

    //assumes that the conversions will all take place within the local area of the init longitude.
    assert(m_radiusMeridional_m > 0.0);
    double latitude_rad = (m_radiusMeridional_m <= 0.0) ? (0.0) : ((north_m / m_radiusMeridional_m) + m_latitudeInitial_rad);
    latitude_deg = latitude_rad * n_Const::c_Convert::dRadiansToDegrees();

    assert(m_radiusSmallCircleLatitude_m > 0.0);
    double longitude_rad = (m_radiusSmallCircleLatitude_m <= 0.0) ? (0.0) : ((east_m / m_radiusSmallCircleLatitude_m) + m_longitudeInitial_rad);
    longitude_deg = longitude_rad * n_Const::c_Convert::dRadiansToDegrees();
};

double FlatEarth::dGetLinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(const double& latitude1_deg, const double& longitude1_deg, const double& latitude2_deg, const double& longitude2_deg)
{
    double north1_m(0.0);
    double east1_m(0.0);
    ConvertLatLong_degToNorthEast_m(latitude1_deg, longitude1_deg, north1_m, east1_m);
    double north2_m(0.0);
    double east2_m(0.0);
    ConvertLatLong_degToNorthEast_m(latitude2_deg, longitude2_deg, north2_m, east2_m);
    double dReturn = std::pow((std::pow((north2_m - north1_m), 2.0) + std::pow((east2_m - east1_m), 2.0)), 0.5);
    return (dReturn);
}

double FlatEarth::dGetLinearDistance_m_Lat1Long1_rad_To_Lat2Long2_rad(const double& latitude1_rad, const double& longitude1_rad, const double& latitude2_rad, const double& longitude2_rad)
{
    double north1_m(0.0);
    double east1_m(0.0);
    ConvertLatLong_radToNorthEast_m(latitude1_rad, longitude1_rad, north1_m, east1_m);
    double north2_m(0.0);
    double east2_m(0.0);
    ConvertLatLong_radToNorthEast_m(latitude2_rad, longitude2_rad, north2_m, east2_m);
    double dReturn = std::pow((std::pow((north2_m - north1_m), 2.0) + std::pow((east2_m - east1_m), 2.0)), 0.5);
    return (dReturn);
};

}       //namespace utilities
}       //namespace common
}       //namespace uxas
