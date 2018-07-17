// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Convert.h
 * Author: steve
 *
 * Created on January 13, 2014, 8:12 PM
 */

#ifndef CONST_CONV_H
#define    CONST_CONV_H

#include <cmath>
#include <cassert>

namespace n_Const
{

/*! \class c_Convert
        \brief this class contains "singleton" constants for unit conversions.

     *  @par Description:
     * 
     * @par Highlights:
     * <ul style="padding-left:1em;margin-left:0">
     * <li>  - 
     * 
     * </ul> @n
     */
    class c_Convert
    {
    public: //constants

        // in-process socket addresses
        /*! @name In-Process Socket Addresses
         *   
         */
        ///@{
        //! 
        ///@}

        // thread control messages
        /*! @name Thread Control Messages
         *   
         */
        ///@{
        //! 

        /*! \brief convert from MilesPerHour to MetersPerSecond  */
        static const double& dMilesPerHourToMetersPerSecond() {
            static double dValue(0.44704);
            return (dValue);
        };

        /*! \brief convert from MetersPerSecond to MilesPerHour  */
        static const double& dMetersPerSecondToMilesPerHour() {
            static double dValue(2.23694);
            return (dValue);
        };
        
        /*! \brief convert from MetersPerSecond to MilesPerHour  */
        static const double& dMetersPerSecondToKnots() {
            static double dValue(1.94384);
            return (dValue);
        };
        
        /*! \brief convert from MetersPerSecond to MilesPerHour  */
        static const double& dKnotsToMetersPerSecond() {
            static double dValue(0.514444);
            return (dValue);
        };

        /*! \brief convert from meters to feet  */
        static const double& dMetersToFeet() {
            static double dValue(3.280839895);
            return (dValue);
        };

        /*! \brief convert from feet to meters  */
        static const double& dFeetToMeters() {
            static double dValue(0.3048);
            return (dValue);
        };

        /*! \brief convert from degrees to radians  */
        static const double toRadians(const double& degrees) {
            static double dValue(0.01745329251994);
            return (dValue * degrees);
        };

        /*! \brief convert from degrees to radians  */
        static const double& dDegreesToRadians() {
            static double dValue(0.01745329251994);
            return (dValue);
        };

        /*! \brief convert from radians to degrees  */
        static const double toDegrees(const double& radians) {
            static double dValue(57.29577951308232);
            return (dValue * radians);
        };

        /*! \brief convert from radians to degrees  */
        static const double& dRadiansToDegrees() {
            static double dValue(57.29577951308232);
            return (dValue);
        };

        /*! \brief convert PI  */
        static const double& dPi() {
            static double dValue(3.14159265359);
            return (dValue);
        };

        /*! \brief convert PI/2.0  */
        static const double& dPiO2() {
            static double dValue(dPi()/2.0);
            return (dValue);
        };

        /*! \brief convert 3.0*PI/2.0  */
        static const double& d3PiO2() {
            static double dValue(3.0*dPi()/2.0);
            return (dValue);
        };

        /*! \brief convert PI/8.0  */
        static const double& dPiO8() {
            static double dValue(dPi()/8.0);
            return (dValue);
        };

        /*! \brief convert PI/10.0  */
        static const double& dPiO10() {
            static double dValue(dPi()/10.0);
            return (dValue);
        };

        /*! \brief convert PI/18.0  */
        static const double& dPiO18() {
            static double dValue(dPi()/18.0);
            return (dValue);
        };

        /*! \brief convert 2*PI  */
        static const double& dTwoPi() {
            static double dValue(2.0 * dPi());
            return (dValue);
        };
        
        /*! \brief gravitational acceleration ft/sec2 */
        static const double& dGravity_fps2() {
            static double dValue(32.174);    // ft/sec^2
            return (dValue);
        };

        /*! \brief gravitational acceleration m/sec^2 */
        static const double& dGravity_mps2() {
            static double dValue(9.80665);    // m/sec^2
            return (dValue);
        };

        
        enum enRelationalOperators
        {
            enGreater,
            enGreaterEqual,
            enLess,
            enLessEqual,
            enEqual,
            enTotalRelationalOperators
        };

        static bool bCompareDouble(double dArgument1, double dArgument2, enRelationalOperators relOperator, double dEpsilon = 1.0e-9) {
            bool bReturn(false);

            switch (relOperator) {
                case enGreater:
                    bReturn = (dArgument1 > dArgument2);
                    break;
                case enGreaterEqual:
                    bReturn = (bCompareDouble(dArgument1, dArgument2, enGreater) || bCompareDouble(dArgument1, dArgument2, enEqual, dEpsilon));
                    break;
                case enLess:
                    bReturn = (dArgument1 < dArgument2);
                    break;
                case enLessEqual:
                    bReturn = (bCompareDouble(dArgument1, dArgument2, enLess) || bCompareDouble(dArgument1, dArgument2, enEqual, dEpsilon));
                    break;
                default:
                case enEqual:
                    bReturn = (std::fabs(dArgument1 - dArgument2) <= dEpsilon);
                    break;
            };
            return (bReturn);
        };

        static bool bCompareFloat(float fArgument1, float fArgument2, enRelationalOperators relOperator, float fEpsilon = 1.0e-9) {
            bool bReturn(false);

            switch (relOperator) {
                case enGreater:
                    bReturn = (fArgument1 > fArgument2);
                    break;
                case enGreaterEqual:
                    bReturn = (bCompareFloat(fArgument1, fArgument2, enGreater) || bCompareFloat(fArgument1, fArgument2, enEqual, fEpsilon));
                    break;
                case enLess:
                    bReturn = (fArgument1 < fArgument2);
                    break;
                case enLessEqual:
                    bReturn = (bCompareFloat(fArgument1, fArgument2, enLess) || bCompareFloat(fArgument1, fArgument2, enEqual, fEpsilon));
                    break;
                default:
                case enEqual:
                    bReturn = (std::fabs(fArgument1 - fArgument2) <= fEpsilon);
                    break;
            };
            return (bReturn);
        };

    static double dNormalizeAngleRad(double dAngleRad,double dAngleReference=(-dPi()))
    {
        assert( dAngleReference <= 0.0 && dAngleReference >= -dTwoPi() );

        double dModAngle = std::fmod(dAngleRad,dTwoPi());
        if( bCompareDouble(dModAngle, dAngleReference, enLess) )
        {
            dModAngle += dTwoPi();
        }
        else if( bCompareDouble(dModAngle, (dAngleReference+dTwoPi()), enGreaterEqual) )
        {
            dModAngle -= dTwoPi();
        }
        return(dModAngle);
    }
    static double dNormalizeAngleDeg(double dAngleDeg,double dAngleReference=(-180.0))
    {
        const double deg360 = 360.0;
        
        assert( dAngleReference <= 0.0 && dAngleReference >= -deg360 );

        double dModAngle = fmod(dAngleDeg,deg360);
        if( bCompareDouble(dModAngle, dAngleReference, enLess) )
        {
            dModAngle += deg360;
        }
        else if( bCompareDouble(dModAngle, (dAngleReference+deg360), enGreaterEqual) )
        {
            dModAngle -= deg360;
        }
        return(dModAngle);
    }
    static float fNormalizeAngleDeg(float fAngleDeg,float fAngleReference=(-180.0))
    {
        const float deg360 = 360.0f;
        
        assert( fAngleReference <= 0.0 && fAngleReference >= -deg360 );

        float fModAngle = fmod(fAngleDeg,deg360);
        if( bCompareFloat(fModAngle, fAngleReference, enLess) )
        {
            fModAngle += deg360;
        }
        else if( bCompareFloat(fModAngle, (fAngleReference+deg360), enGreaterEqual) )
        {
            fModAngle -= deg360;
        }
        return(fModAngle);
    }
        
    static int iRound(double dNumber)
    {
        // rounds rdNumber to the nearest integer.
        return(int(dNumber + 0.5));
    };
    static double dRound(double dNumber,const double dDecimalPlace)
    {
        // rounds rdNumber to the dDecimalPlace decimal place.
        // i.e. vRound(123456.123456,1e-2) => 123456.12 and vRound(123456.123456,1e2) => 123500.00
        dNumber = floor(dNumber/dDecimalPlace + 0.5)*dDecimalPlace;
        return(dNumber);
    };
    static void vRound(double& rdNumber,const double dDecimalPlace)
    {
        // rounds rdNumber to the dDecimalPlace decimal place.
        // i.e. vRound(123456.123456,1e-2) => 123456.12 and vRound(123456.123456,1e2) => 123500.00
        rdNumber = floor(rdNumber/dDecimalPlace + 0.5)*dDecimalPlace;
    };
    
        
        
        
        ///@}

    }; //class c_Convert

}; //namespace n_Const


#endif    /* CONST_CONV_H */

