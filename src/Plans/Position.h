// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

//
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION IS RELEASED "AS IS." THE
//    U.S.GOVERNMENT MAKES NO WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, CONCERNING
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION, INCLUDING, WITHOUT LIMITATION,
//    ANY WARRANTIES OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT
//    WILL THE U.S. GOVERNMENT BE LIABLE FOR ANY DAMAGES, INCLUDING ANY LOST PROFITS,
//    LOST SAVINGS OR OTHER INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE,
//    OR INABILITY TO USE, THIS SOFTWARE OR ANY ACCOMPANYING DOCUMENTATION, EVEN IF
//    INFORMED IN ADVANCE OF THE POSSIBILITY OF SUCH DAMAGES.
//
// Position.h: interface for the CPosition class.
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_POSITION_H__685A57A9_6564_42A2_9CCD_C5814BE13A53__INCLUDED_)
#define AFX_POSITION_H__685A57A9_6564_42A2_9CCD_C5814BE13A53__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//#include "GlobalDefines.h"
#include "UnitConversions.h"    // static linearization point, but can be changed
#include "FlatEarth.h"  // non-static linearization point

#include <ostream>
#include <vector>

namespace n_FrameworkLib
{

    class CPosition
    {
    public:
        enum enPositionUnits
        {
            unitsFeet,
            unitsMeters,
            unitsLatitudeLongitude_rad,
            unitsLatitudeLongitude_deg,
            unitsNumber
        };

        
    public:

        CPosition(const double& north_m,
                const double& east_m,
                const double& altitude_m = 0.0)
        : m_north_m(north_m),
        m_east_m(east_m),
        m_altitude_m(altitude_m)
        { };

        CPosition(const double& latitude_rad,
                const double& longitude_rad,
                const double& altitude_m,
                const double& dummy
                )
        : m_altitude_m(altitude_m),m_latitude_rad(latitude_rad),m_longitude_rad(longitude_rad)
        {
            uxas::common::utilities::CUnitConversions unitConversions;
            unitConversions.ConvertLatLong_radToNorthEast_m(latitude_rad, longitude_rad, m_north_m, m_east_m);
        };

        CPosition(const double& latitude_rad,
                const double& longitude_rad,
                const double& altitude_m,
                uxas::common::utilities::FlatEarth& flatEarth
                )
        : m_altitude_m(altitude_m),m_latitude_rad(latitude_rad),m_longitude_rad(longitude_rad)
        {
            flatEarth.ConvertLatLong_radToNorthEast_m(latitude_rad, longitude_rad, m_north_m, m_east_m);
        };

        CPosition(){};

        virtual ~CPosition() { };

        // copy constructer

        CPosition(const CPosition& rhs) {
            m_north_m = rhs.m_north_m;
            m_east_m = rhs.m_east_m;
            m_altitude_m = rhs.m_altitude_m;
            m_latitude_rad = rhs.m_latitude_rad;
            m_longitude_rad = rhs.m_longitude_rad;
        }

        void operator=(const CPosition& rhs) {
            m_north_m = rhs.m_north_m;
            m_east_m = rhs.m_east_m;
            m_altitude_m = rhs.m_altitude_m;
            m_latitude_rad = rhs.m_latitude_rad;
            m_longitude_rad = rhs.m_longitude_rad;
        }

        void operator=(const double& rhs) {
            m_north_m = rhs;
            m_east_m = rhs;
        }

        bool operator==(const CPosition& rhs) {
            return (relativeDistance2D_m(rhs) <= 1.0e-3);
        }

        bool operator!=(const CPosition& rhs) {
            return (relativeDistance2D_m(rhs) > 1.0e-3);
        }

        const std::ostream& operator<<(std::ostream &os)const {
            os << "[" << m_north_m << ",";
            os << m_east_m << ",";
            os << m_altitude_m << "]";
            return os;
        }
    public:

        double relativeAngle2D_rad(const CPosition& posPoint) {
            // returns the relative angle between the two
            // NOTE: the point passed in is located at the vertex of the angle
            double dNorth = m_north_m - posPoint.m_north_m;
            double dEast = m_east_m - posPoint.m_east_m;
            return (n_Const::c_Convert::dNormalizeAngleRad(atan2(dNorth, dEast), 0.0));
        };

        const double relativeAngle2D_rad(const CPosition& posPoint)const {
            // returns the relative angle between the two
            // NOTE: the point passed in is located at the vertex of the angle
            double dNorth = m_north_m - posPoint.m_north_m;
            double dEast = m_east_m - posPoint.m_east_m;
            return (n_Const::c_Convert::dNormalizeAngleRad(atan2(dNorth, dEast), 0.0));
        };

        double relativeDistance2D_m(const CPosition& posPoint) {
            using namespace std;

            // returns the distance between this point and another
            double dNorth = m_north_m - posPoint.m_north_m;
            double dEast = m_east_m - posPoint.m_east_m;

            return (sqrt((dNorth * dNorth) + (dEast * dEast)));
        };

        double relativeDistance2D_m(const CPosition& posPoint)const {
            using namespace std;

            // returns the distance between this point and another
            double dNorth = m_north_m - posPoint.m_north_m;
            double dEast = m_east_m - posPoint.m_east_m;

            return (sqrt((dNorth * dNorth) + (dEast * dEast)));
        };

        double manhattanDistance_m(const CPosition& posPoint)const {
            using namespace std;

            // returns the Manhattan distance between this point and another
            double north_m = m_north_m - posPoint.m_north_m;
            double east_m = m_east_m - posPoint.m_east_m;

            return (north_m + east_m);
        };

        double relativeDistanceAngle2D_m(const CPosition& posPoint, double& rdAngleRelative_rad) {
            // returns the distance between this point and another
            // also calculates the relative angle between the two
            // NOTE: the point passed in is located at the vertex of the angle

            double dNorth = m_north_m - posPoint.m_north_m;
            double dEast = m_east_m - posPoint.m_east_m;
            rdAngleRelative_rad = n_Const::c_Convert::dNormalizeAngleRad(atan2(dNorth, dEast), 0.0);
            return (sqrt((dNorth * dNorth) + (dEast * dEast)));
        };

        CPosition operator-() {
            return (CPosition((-m_north_m),
                    (-m_east_m),
                    m_altitude_m));
        };

        CPosition operator*(double dMultiplier) //two dimensional multiplication
        {
            return (CPosition((m_north_m *= dMultiplier),
                    (m_east_m *= dMultiplier),
                    m_altitude_m));
        };

        void operator*=(double dMultiplier) //two dimensional multiplication
        {
            m_north_m *= dMultiplier;
            m_east_m *= dMultiplier;
        };

        CPosition operator+(CPosition& rhs) {
            return (CPosition((m_north_m + rhs.m_north_m),
                    (m_east_m + rhs.m_east_m),
                    m_altitude_m));
            //reGetAltitude_m()+rhs.reGetAltitude_m()));    //assume only want to deal with 2d coordinates
        };

        CPosition operator+(const CPosition& rhs) {
            return (CPosition((m_north_m + rhs.m_north_m),
                    (m_east_m + rhs.m_east_m),
                    m_altitude_m));
            //reGetAltitude_m()+rhs.reGetAltitude_m()));    //assume only want to deal with 2d coordinates
        };

        CPosition operator-(CPosition& rhs) {
            return (CPosition((m_north_m - rhs.m_north_m),
                    (m_east_m - rhs.m_east_m),
                    m_altitude_m));
            //reGetAltitude_m()+rhs.reGetAltitude_m()));    //assume only want to deal with 2d coordinates
        };

        CPosition operator-(const CPosition& rhs) {
            return (CPosition((m_north_m - rhs.m_north_m),
                    (m_east_m - rhs.m_east_m),
                    m_altitude_m));
            //reGetAltitude_m()+rhs.reGetAltitude_m()));    //assume only want to deal with 2d coordinates
        };

        void operator+=(const CPosition& rhs) {
            m_north_m += rhs.m_north_m;
            m_east_m += rhs.m_east_m;
            //reGetAltitude_m() += rhs.reGetAltitude_m();    //assume only want to deal with 2d coordinates
        };

        void operator-=(const CPosition& rhs) {
            m_north_m -= rhs.m_north_m;
            m_east_m -= rhs.m_east_m;
            //reGetAltitude_m() -= rhs.reGetAltitude_m();    //assume only want to deal with 2d coordinates
        };

        void operator/=(const double& dScalar) {
            m_north_m /= dScalar;
            m_east_m /= dScalar;
            //reGetAltitude_m() -= rhs.reGetAltitude_m();    //assume only want to deal with 2d coordinates
        };

        double absoluteDistance2D_m() {
            // returns the distance between this point and the orign    -> 2D
            return (pow((pow(m_north_m, 2) + pow(m_east_m, 2)), 0.5));
        };

        void TransformPoint2D(const CPosition& posPoint, const double rdAngleRotation_rad) {
            double dCosTheta = cos(rdAngleRotation_rad);
            double dSinTheta = sin(rdAngleRotation_rad);
            double dPositionNorthNew = m_north_m - posPoint.m_north_m;
            double dPositionEastNew = m_east_m - posPoint.m_east_m;
            m_north_m = dPositionNorthNew * dCosTheta + dPositionEastNew*dSinTheta;
            m_east_m = dPositionEastNew * dCosTheta - dPositionNorthNew*dSinTheta;
        }

        void ReTransformPoint2D(const CPosition& posPoint, const double rdAngleRotation_rad) {
            double dCosTheta = cos(rdAngleRotation_rad);
            double dSinTheta = sin(rdAngleRotation_rad);

            double dRotationNorthNew = m_north_m * dCosTheta - m_east_m * dSinTheta;
            double dRotationEastNew = m_north_m * dSinTheta + m_east_m * dCosTheta;

            m_north_m = dRotationNorthNew + posPoint.m_north_m;
            m_east_m = dRotationEastNew + posPoint.m_east_m;
        }

    public:
        double m_north_m = 0.0;
        double m_east_m = 0.0;
        double m_altitude_m = 0.0;

        double m_latitude_rad = 0.0;
        double m_longitude_rad = 0.0;

    };

    class rasCPositionID : public CPosition
    {
    public:

        enum enType
        {
            typNone,
            typVehicle,
            typObjective,
            typTarget,
            typObjective_Start,
            typObjective_End,
            typVisibilityVertex,
            typRecovery,
            typTotal
        };
    public:

        rasCPositionID(CPosition posPosition, enType typPositionType = typNone)
        : CPosition(posPosition),
		m_iID(-1),
        m_typPositionType(typNone) { };

        rasCPositionID(int iID, CPosition posPosition, enType typPositionType = typNone)
        : CPosition(posPosition),
		m_iID(iID),
        m_typPositionType(typPositionType) { };

        rasCPositionID(int iID = -1, enType typPositionType = typNone)
        : m_iID(iID),
        m_typPositionType(typPositionType) { };

        rasCPositionID(const rasCPositionID& rhs) {
            CPosition::operator=(rhs);
            iGetID() = rhs.iGetID();
            typGetPositionType() = rhs.typGetPositionType();
            posGetEndPoint() = rhs.posGetEndPoint();
        };

        void operator=(const rasCPositionID& rhs) {
            CPosition::operator=(rhs);
            iGetID() = rhs.iGetID();
            typGetPositionType() = rhs.typGetPositionType();
            posGetEndPoint() = rhs.posGetEndPoint();
        };

    public:

        int& iGetID() {
            return (m_iID);
        };

        const int& iGetID()const {
            return (m_iID);
        };

        enType& typGetPositionType() {
            return (m_typPositionType);
        };

        const enType& typGetPositionType()const {
            return (m_typPositionType);
        };

        CPosition& posGetEndPoint() {
            return (m_posEndPoint);
        };

        const CPosition& posGetEndPoint()const {
            return (m_posEndPoint);
        };

    protected:
        int m_iID;
        enType m_typPositionType;
        CPosition m_posEndPoint;
    };

    typedef std::vector<rasCPositionID> V_POSITON_ID_t;
    typedef std::vector<rasCPositionID>::iterator V_POSITON_ID_IT_t;
    typedef std::vector<rasCPositionID>::const_iterator V_POSITON_ID_CONST_IT_t;

    typedef std::vector<CPosition> V_POSITION_t;
    typedef std::vector<CPosition>::iterator V_POSITION_IT_t;
    typedef std::vector<CPosition>::const_iterator V_POSITION_CONST_IT_t;

    std::ostream &operator<<(std::ostream &os, const CPosition& posRhs);

}; //namespace n_FrameworkLib

#endif // !defined(AFX_POSITION_H__685A57A9_6564_42A2_9CCD_C5814BE13A53__INCLUDED_)
