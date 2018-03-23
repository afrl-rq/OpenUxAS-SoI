// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// FlatEarth.h: interface for the FlatEarth class.
//
///
///
///
///
///
///
//////////////////////////////////////////////////////////////////////

/* 
 * File:   FlatEarth.h
 * Author: Steve
 *
 * Created on March 23, 2018
 */


#if !defined(AFX_FLAT_EARTH_H__DA67D2FA_58FA_4A70_A3CF_940808C5F2D9__INCLUDED_)
#define AFX_FLAT_EARTH_H__DA67D2FA_58FA_4A70_A3CF_940808C5F2D9__INCLUDED_

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


/*! \class FlatEarth
    \brief This utility class is used to convert between geographic (Latitude/Longitude)
    and linear (North/East) coordinates. 
        - Latitude/Longitude coordinates are based on the WGS-84 ellipsoid
        - North/East coordinates are in a linear Cartesian coordinate system, tangent to the WGS-84 
          ellipsoid at a given reference location (lat/long)

 * Initialization:
 * - linear coordinates are given with the origin at the 'linearization point'.
 * - the 'linearization point' is set by either the first call to a "ConvertLatLong_xxxToNorthEast_xxx"
 * or by calling "Initialize"
 * - It is an error to call one of the "ConvertNorthEast_xxxToLatLong_xxx" functions before the 
 * 'linearization point' has been initialized. This will result in erroneous results.
 * - the 'linearization point' is not static, therefore a class requiring a common
 * 'linearization point' for all operations must maintain its own instance of FlatEarth, 
 * i.e. as a member variable.
 * NOTE: there is no error checking
 * 
 */
class FlatEarth
{
public:

    FlatEarth() { };

    virtual ~FlatEarth() { };

public:

    void Initialize(const double& latitudeInit_rad, const double& longitudeInit_rad);

    ////////////////////////////////////////////////////////////////////////////
    ////// FROM LAT/LONG TO NORTH/EAST

    /** brief conversion from latitude/longitude in radians to north/east coordinates in feet */
    void ConvertLatLong_radToNorthEast_ft(const double& latitude_rad, const double& longitude_rad, double& north_ft, double& east_ft);
    /** brief conversion from latitude/longitude in radians to north/east coordinates in meters */
    void ConvertLatLong_radToNorthEast_m(const double& latitude_rad, const double& longitude_rad, double& north_m, double& east_m);
    /** brief conversion from latitude/longitude in degrees to north/east coordinates in meters*/
    void ConvertLatLong_degToNorthEast_m(const double& latitude_deg, const double& longitude_deg, double& north_m, double& east_m);
    /** brief conversion from latitude/longitude in degrees to north/east coordinates in feet */
    void ConvertLatLong_degToNorthEast_ft(const double& latitude_deg, const double& longitude_deg, double& north_ft, double& east_ft);
    ////////////////////////////////////////////////////////////////////////////

    ////////////////////////////////////////////////////////////////////////////
    ////// FROM NORTH/EAST TO LAT/LONG

    /** brief conversion from north/east coordinates in meters to latitude/longitude in radians*/
    void ConvertNorthEast_mToLatLong_rad(const double& north_m, const double& east_m, double& latitude_rad, double& longitude_rad);
    /** brief conversion from north/east coordinates in meters to latitude/longitude in degrees*/
    void ConvertNorthEast_mToLatLong_deg(const double& north_m, const double& east_m, double& latitude_deg, double& longitude_deg);
    /** brief conversion from north/east coordinates in feet to latitude/longitude in radians*/
    void ConvertNorthEast_ftToLatLong_rad(const double& north_ft, const double& east_ft, double& latitude_rad, double& longitude_rad);
    /** brief conversion from north/east coordinates in feet to latitude/longitude in degrees*/
    void ConvertNorthEast_ftToLatLong_deg(const double& north_ft, const double& east_ft, double& latitude_deg, double& longitude_deg); 
    
    ////////////////////////////////////////////////////////////////////////////
    ////// LINEAR DISTANCES
    /** brief calculates the linearized distance (meters) between to geographic coordinates (degrees)*/
    double dGetLinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(const double& latitude1_deg, const double& longitude1_deg, const double& latitude2_deg, const double& longitude2_deg);
    /** brief calculates the linearized distance (meters) between to geographic coordinates (radians)*/
    double dGetLinearDistance_m_Lat1Long1_rad_To_Lat2Long2_rad(const double& latitude1_rad, const double& longitude1_rad, const double& latitude2_rad, const double& longitude2_rad);

public:
    // WGS-84 parameters
    const double m_radiusEquatorial_m{6378135.0};
    const double m_flattening{3.352810664724998e-003};
    const double m_eccentricitySquared{6.694379990096503e-003};

protected:

    double m_latitudeInitial_rad{0.0};
    double m_longitudeInitial_rad{0.0};
    double m_radiusMeridional_m{0.0};
    double m_radiusTransverse_m{0.0};
    double m_radiusSmallCircleLatitude_m{0.0};
    bool m_isInitialized{false};

};



/////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////

}; //namespace utilities
}; //namespace common
}; //namespace uxas

#endif // !defined(AFX_FLAT_EARTH_H__DA67D2FA_58FA_4A70_A3CF_940808C5F2D9__INCLUDED_)
