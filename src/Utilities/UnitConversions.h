// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// UnitConversions.h: interface for the CUnitConversions class.
//
/// "CUnitConversions" Class: used to convert between Latitude/Longitude and North/East coordinates. 
///        - Latitude/Longitude coordinates are based on the WGS-84 ellipsoid
///        - North/East coordinates are in a linear Cartesian coordinate system, tangent to the WGS-84 
///          ellipsoid at a given reference location (lat/long)
///
///    "CUnitConversions" uses a static instance of the class "CLinearizationPointsStatic" to manage multiple 
///    linearization locations. Once initialized, coordinate conversions based on these locations are available
/// to all instances of the "CUnitConversions" class. "CLinearizationPointsStatic" contains a container that
/// stores multiple instances of the class "CLinearizationPoint". "CLinearizationPoint" contains all of the
/// parameters necessary to convert between Lat/Long and North/East based on a given initial location.
///
/// If the default, ID=0, "CLinearizationPoint" has not been initialized, then it is initialized the
/// first time one of the "ConvertLatLong_xxxToNorthEast_xxx" functions are called.
///
/// It is an error to call one of the "ConvertNorthEast_xxxToLatLong_xxx" functions before the default
/// "CLinearizationPoint" has been initialized. This will result in erroneous results.
///
/// To add new linearization points call the function "NewLinearizationPoint(...)". The ID of the new
/// point is returned in the argument "szID". After the new point has been added use the ID of the desired
/// "CLinearizationPoint" during calls to the "ConvertLatLong_xxxToNorthEast_xxx" and
/// "ConvertNorthEast_xxxToLatLong_xxx" functions.
///
///
///
///
///
//////////////////////////////////////////////////////////////////////


#if !defined(AFX_UNITCONVERSIONS_H__DA67D2FA_58FA_4A70_A3CF_940808C5F2D9__INCLUDED_)
#define AFX_UNITCONVERSIONS_H__DA67D2FA_58FA_4A70_A3CF_940808C5F2D9__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//#pragma warning(disable: 4786)


#include <cmath>
#include <cassert>
#include <cstddef> //size_t
#include <vector>
#include <memory>       //std::shared_ptr

#ifdef _WIN32
#include <crtdbg.h>        //assert
#endif//#ifndef WIN32

#include "Constants/Convert.h"


namespace uxas
{
namespace common
{
namespace utilities
{


/*! \class CUnitConversions
    \brief This class manages the linear/geographical conversions by exposing the 
 * conversion functions of the static list of @ref CLinearizationPoint s, see @ref CLinearizationPointsStatic.
 * 
 */
class CUnitConversions
{
public:

    CUnitConversions() { };

    virtual ~CUnitConversions() { };

public:

    void Initialize(const double& dLatitudeInit_rad, const double& dLongitudeInit_rad);
    void ReInitialize(const double& dLatitudeInit_rad, const double& dLongitudeInit_rad);

    ////////////////////////////////////////////////////////////////////////////
    ////// FROM LAT/LONG TO NORTH/EAST

    void ConvertLatLong_radToNorthEast_ft(const double& dLatitude_rad, const double& dLongitude_rad, double& dNorth_ft, double& dEast_ft);
    void ConvertLatLong_radToNorthEast_m(const double& dLatitude_rad, const double& dLongitude_rad, double& dNorth_m, double& dEast_m);
    void ConvertLatLong_degToNorthEast_m(const double& dLatitude_deg, const double& dLongitude_deg, double& dNorth_m, double& dEast_m);
    void ConvertLatLong_degToNorthEast_ft(const double& dLatitude_deg, const double& dLongitude_deg, double& dNorth_ft, double& dEast_ft);
    ////////////////////////////////////////////////////////////////////////////

    ////////////////////////////////////////////////////////////////////////////
    ////// FROM NORTH/EAST TO LAT/LONG

    void ConvertNorthEast_mToLatLong_rad(const double& dNorth_m, const double& dEast_m, double& dLatitude_rad, double& dLongitude_rad);
    void ConvertNorthEast_mToLatLong_deg(const double& dNorth_m, const double& dEast_m, double& dLatitude_deg, double& dLongitude_deg);
    void ConvertNorthEast_ftToLatLong_rad(const double& dNorth_ft, const double& dEast_ft, double& dLatitude_rad, double& dLongitude_rad);
    void ConvertNorthEast_ftToLatLong_deg(const double& dNorth_ft, const double& dEast_ft, double& dLatitude_deg, double& dLongitude_deg); 
    
    ////////////////////////////////////////////////////////////////////////////
    ////// LINEAR DISTANCES
    double dGetLinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(const double& dLatitude1_deg, const double& dLongitude1_deg, const double& dLatitude2_deg, const double& dLongitude2_deg);
    double dGetLinearDistance_m_Lat1Long1_rad_To_Lat2Long2_rad(const double& dLatitude1_rad, const double& dLongitude1_rad, const double& dLatitude2_rad, const double& dLongitude2_rad);

public:
    // WGS-84 parameters
    const double m_dRadiusEquatorial_m{6378135.0};
    const double m_dFlattening{3.352810664724998e-003};
    const double m_dEccentricitySquared{6.694379990096503e-003};

protected:

    static double m_dLatitudeInitial_rad;
    static double m_dLongitudeInitial_rad;
    static double m_dRadiusMeridional_m;
    static double m_dRadiusTransverse_m;
    static double m_dRadiusSmallCircleLatitude_m;
    static bool m_bInitialized;

};



/////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////

}; //namespace log
}; //namespace common
}; //namespace uxas

#endif // !defined(AFX_UNITCONVERSIONS_H__DA67D2FA_58FA_4A70_A3CF_940808C5F2D9__INCLUDED_)
