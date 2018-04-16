// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// UnitConversions.cpp
//
//////////////////////////////////////////////////////////////////////

#include "UnitConversions.h"


namespace uxas
{
namespace common
{
namespace utilities
{

double CUnitConversions::m_dLatitudeInitial_rad{0.0};
double CUnitConversions::m_dLongitudeInitial_rad{0.0};
double CUnitConversions::m_dRadiusMeridional_m{0.0};
double CUnitConversions::m_dRadiusTransverse_m{0.0};
double CUnitConversions::m_dRadiusSmallCircleLatitude_m{0.0};
bool CUnitConversions::m_bInitialized{false};

void CUnitConversions::Initialize(const double& dLatitudeInit_rad, const double& dLongitudeInit_rad)
{
    //no re-initialization allowed!!!!
    if (!m_bInitialized)
    {
        //assumes that the conversions will all take place within the local area of the initial latitude/longitude.
        m_dLatitudeInitial_rad = dLatitudeInit_rad;
        m_dLongitudeInitial_rad = dLongitudeInit_rad;

        double dDenominatorMeridional = std::pow((1.0 - (m_dEccentricitySquared * std::pow(std::sin(dLatitudeInit_rad), 2.0))), (3.0 / 2.0));
        assert(dDenominatorMeridional > 0.0);
        m_dRadiusMeridional_m = (dDenominatorMeridional <= 0.0) ? (0.0) : (m_dRadiusEquatorial_m * (1.0 - m_dEccentricitySquared) / dDenominatorMeridional);
        double dDenominatorTransverse = pow((1.0 - (m_dEccentricitySquared * std::pow(std::sin(dLatitudeInit_rad), 2.0))), 0.5);
        assert(dDenominatorTransverse > 0.0);
        m_dRadiusTransverse_m = (dDenominatorTransverse <= 0.0) ? (0.0) : (m_dRadiusEquatorial_m / dDenominatorTransverse);
        m_dRadiusSmallCircleLatitude_m = m_dRadiusTransverse_m * cos(dLatitudeInit_rad);
        m_bInitialized = true;
    }
};

void CUnitConversions::ReInitialize(const double& dLatitudeInit_rad, const double& dLongitudeInit_rad)
{
//    m_bInitialized = false;
//    Initialize(dLatitudeInit_rad,dLongitudeInit_rad);
//#error "ERROR: CUnitConversions::ReInitialize::   reiitialize is no longer allowed!!!"
};

////////////////////////////////////////////////////////////////////////////
////// FROM LAT/LONG TO NORTH/EAST

void CUnitConversions::ConvertLatLong_radToNorthEast_ft(const double& dLatitude_rad, const double& dLongitude_rad, double& dNorth_ft, double& dEast_ft)
{
    //assumes that the conversions will all take place within the local area of the init longitude.
    if (!m_bInitialized)
    {
        Initialize(dLatitude_rad, dLongitude_rad);
    }

    double dNorth_m = m_dRadiusMeridional_m * (dLatitude_rad - m_dLatitudeInitial_rad);
    double dEast_m = m_dRadiusSmallCircleLatitude_m * (dLongitude_rad - m_dLongitudeInitial_rad);

    dNorth_ft = dNorth_m * n_Const::c_Convert::dMetersToFeet();
    dEast_ft = dEast_m * n_Const::c_Convert::dMetersToFeet();
};

void CUnitConversions::ConvertLatLong_radToNorthEast_m(const double& dLatitude_rad, const double& dLongitude_rad, double& dNorth_m, double& dEast_m)
{
    //assumes that the conversions will all take place within the local area of the init longitude.
    if (!m_bInitialized)
    {
        Initialize(dLatitude_rad, dLongitude_rad);
    }

    dNorth_m = m_dRadiusMeridional_m * (dLatitude_rad - m_dLatitudeInitial_rad);
    dEast_m = m_dRadiusSmallCircleLatitude_m * (dLongitude_rad - m_dLongitudeInitial_rad);
};

void CUnitConversions::ConvertLatLong_degToNorthEast_m(const double& dLatitude_deg, const double& dLongitude_deg, double& dNorth_m, double& dEast_m)
{
    double dLatitude_rad = dLatitude_deg * n_Const::c_Convert::dDegreesToRadians();
    double dLongitude_rad = dLongitude_deg * n_Const::c_Convert::dDegreesToRadians();

    //assumes that the conversions will all take place within the local area of the init longitude.
    if (!m_bInitialized)
    {
        Initialize(dLatitude_rad, dLongitude_rad);
    }

    dNorth_m = m_dRadiusMeridional_m * (dLatitude_rad - m_dLatitudeInitial_rad);
    dEast_m = m_dRadiusSmallCircleLatitude_m * (dLongitude_rad - m_dLongitudeInitial_rad);
};

void CUnitConversions::ConvertLatLong_degToNorthEast_ft(const double& dLatitude_deg, const double& dLongitude_deg, double& dNorth_ft, double& dEast_ft)
{
    double dLatitude_rad = dLatitude_deg * n_Const::c_Convert::dDegreesToRadians();
    double dLongitude_rad = dLongitude_deg * n_Const::c_Convert::dDegreesToRadians();

    //assumes that the conversions will all take place within the local area of the init longitude.
    if (!m_bInitialized)
    {
        Initialize(dLatitude_rad, dLongitude_rad);
    }

    double dNorth_m = m_dRadiusMeridional_m * (dLatitude_rad - m_dLatitudeInitial_rad);
    double dEast_m = m_dRadiusSmallCircleLatitude_m * (dLongitude_rad - m_dLongitudeInitial_rad);

    dNorth_ft = dNorth_m * n_Const::c_Convert::dMetersToFeet();
    dEast_ft = dEast_m * n_Const::c_Convert::dMetersToFeet();
};
////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////
////// FORM NORTH/EAST TO LAT/LONG

void CUnitConversions::ConvertNorthEast_mToLatLong_rad(const double& dNorth_m, const double& dEast_m, double& dLatitude_rad, double& dLongitude_rad)
{
    //assumes that the conversions will all take place within the local area of the init longitude.
    assert(m_dRadiusMeridional_m > 0.0);
    dLatitude_rad = (m_dRadiusMeridional_m <= 0.0) ? (0.0) : ((dNorth_m / m_dRadiusMeridional_m) + m_dLatitudeInitial_rad);
    assert(m_dRadiusSmallCircleLatitude_m > 0.0);
    dLongitude_rad = (m_dRadiusSmallCircleLatitude_m <= 0.0) ? (0.0) : ((dEast_m / m_dRadiusSmallCircleLatitude_m) + m_dLongitudeInitial_rad);
};

void CUnitConversions::ConvertNorthEast_mToLatLong_deg(const double& dNorth_m, const double& dEast_m, double& dLatitude_deg, double& dLongitude_deg)
{
    //assumes that the conversions will all take place within the local area of the init longitude.
    assert(m_dRadiusMeridional_m > 0.0);
    dLatitude_deg = (m_dRadiusMeridional_m <= 0.0) ? (0.0) : ((dNorth_m / m_dRadiusMeridional_m) + m_dLatitudeInitial_rad) * n_Const::c_Convert::dRadiansToDegrees();
    assert(m_dRadiusSmallCircleLatitude_m > 0.0);
    dLongitude_deg = (m_dRadiusSmallCircleLatitude_m <= 0.0) ? (0.0) : ((dEast_m / m_dRadiusSmallCircleLatitude_m) + m_dLongitudeInitial_rad) * n_Const::c_Convert::dRadiansToDegrees();
};

void CUnitConversions::ConvertNorthEast_ftToLatLong_rad(const double& dNorth_ft, const double& dEast_ft, double& dLatitude_rad, double& dLongitude_rad)
{
    double dNorth_m = dNorth_ft * n_Const::c_Convert::dFeetToMeters();
    double dEast_m = dEast_ft * n_Const::c_Convert::dFeetToMeters();

    //assumes that the conversions will all take place within the local area of the init longitude.
    assert(m_dRadiusMeridional_m > 0.0);
    dLatitude_rad = (m_dRadiusMeridional_m <= 0.0) ? (0.0) : ((dNorth_m / m_dRadiusMeridional_m) + m_dLatitudeInitial_rad);

    assert(m_dRadiusSmallCircleLatitude_m > 0.0);
    dLongitude_rad = (m_dRadiusSmallCircleLatitude_m <= 0.0) ? (0.0) : ((dEast_m / m_dRadiusSmallCircleLatitude_m) + m_dLongitudeInitial_rad);
};

void CUnitConversions::ConvertNorthEast_ftToLatLong_deg(const double& dNorth_ft, const double& dEast_ft, double& dLatitude_deg, double& dLongitude_deg)
{
    double dNorth_m = dNorth_ft * n_Const::c_Convert::dFeetToMeters();
    double dEast_m = dEast_ft * n_Const::c_Convert::dFeetToMeters();

    //assumes that the conversions will all take place within the local area of the init longitude.
    assert(m_dRadiusMeridional_m > 0.0);
    double dLatitude_rad = (m_dRadiusMeridional_m <= 0.0) ? (0.0) : ((dNorth_m / m_dRadiusMeridional_m) + m_dLatitudeInitial_rad);
    dLatitude_deg = dLatitude_rad * n_Const::c_Convert::dRadiansToDegrees();

    assert(m_dRadiusSmallCircleLatitude_m > 0.0);
    double dLongitude_rad = (m_dRadiusSmallCircleLatitude_m <= 0.0) ? (0.0) : ((dEast_m / m_dRadiusSmallCircleLatitude_m) + m_dLongitudeInitial_rad);
    dLongitude_deg = dLongitude_rad * n_Const::c_Convert::dRadiansToDegrees();
};

double CUnitConversions::dGetLinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(const double& dLatitude1_deg, const double& dLongitude1_deg, const double& dLatitude2_deg, const double& dLongitude2_deg)
{
    double dNorth1_m(0.0);
    double dEast1_m(0.0);
    ConvertLatLong_degToNorthEast_m(dLatitude1_deg, dLongitude1_deg, dNorth1_m, dEast1_m);
    double dNorth2_m(0.0);
    double dEast2_m(0.0);
    ConvertLatLong_degToNorthEast_m(dLatitude2_deg, dLongitude2_deg, dNorth2_m, dEast2_m);
    double dReturn = std::pow((std::pow((dNorth2_m - dNorth1_m), 2.0) + std::pow((dEast2_m - dEast1_m), 2.0)), 0.5);
    return (dReturn);
}

double CUnitConversions::dGetLinearDistance_m_Lat1Long1_rad_To_Lat2Long2_rad(const double& dLatitude1_rad, const double& dLongitude1_rad, const double& dLatitude2_rad, const double& dLongitude2_rad)
{
    double dNorth1_m(0.0);
    double dEast1_m(0.0);
    ConvertLatLong_radToNorthEast_m(dLatitude1_rad, dLongitude1_rad, dNorth1_m, dEast1_m);
    double dNorth2_m(0.0);
    double dEast2_m(0.0);
    ConvertLatLong_radToNorthEast_m(dLatitude2_rad, dLongitude2_rad, dNorth2_m, dEast2_m);
    double dReturn = std::pow((std::pow((dNorth2_m - dNorth1_m), 2.0) + std::pow((dEast2_m - dEast1_m), 2.0)), 0.5);
    return (dReturn);
};

}       //namespace utilities
}       //namespace common
}       //namespace uxas
