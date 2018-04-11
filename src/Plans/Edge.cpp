// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

// Waypoint.cpp: implementation of the CWaypoint class.
//
//////////////////////////////////////////////////////////////////////

#include "Edge.h"

namespace n_FrameworkLib
{

CPosition cnst_posDefault;

std::ostream &operator << (std::ostream &os,const CEdge& edgeRhs)
{
#ifdef MATLAB_PLOT
    os    << "[" << edgeRhs.first << ","
        <<  edgeRhs.second << ","
        << edgeRhs.iGetLength() << "]";
        return os;
#else    //#ifdef MATLAB_PLOT
    os << edgeRhs.first << ","
        << edgeRhs.second << ","
        << edgeRhs.iGetLength();
    return os;
#endif    //#ifdef MATLAB_PLOT

}

#define SAME_SIGNS(a,b) ((a==0)?(1):(a/fabs(a))) == ((b==0)?(1):(b/fabs(b)))

    bool CEdge::bFindIntersection(const CPosition& posPointA1, const CPosition& posPointA2, const CPosition& posPointB1, const CPosition& posPointB2, CPosition& posIntersectionPoint)
    {
        bool bReturn(false); //i.e. no intersection
        //check for intersection of segments
        //copy intersection point to "posIntersectionPoint"

        /* lines_intersect:  AUTHOR: Mukesh Prasad
         *
         *   This function computes whether two line segments,
         *   respectively joining the input points (x1,y1) -- (x2,y2)
         *   and the input points (x3,y3) -- (x4,y4) intersect.
         *   If the lines intersect, the output variables x, y are
         *   set to coordinates of the point of intersection.
         *
         *   All values are in integers.  The returned value is rounded
         *   to the nearest integer point.
         *
         *   If non-integral grid points are relevant, the function
         *   can easily be transformed by substituting floating point
         *   calculations instead of integer calculations.
         *
         *   Entry
         *        x1, y1,  x2, y2   Coordinates of endpoints of one segment.
         *        x3, y3,  x4, y4   Coordinates of endpoints of other segment.
         *
         *   Exit
         *        x, y              Coordinates of intersection point.
         *
         *   The value returned by the function is one of:
         *
         *        DONT_INTERSECT    0
         *        DO_INTERSECT      1
         *        COLLINEAR         2
         *
         * Error conditions:
         *
         *     Depending upon the possible ranges, and particularly on 16-bit
         *     computers, care should be taken to protect from overflow.
         *
         *     In the following code, 'long' values have been used for this
         *     purpose, instead of 'int64_t'.
         *
         */

        /* First line segment */
        double dX1(posPointA1.m_east_m);
        double dY1(posPointA1.m_north_m);
        double dX2(posPointA2.m_east_m);
        double dY2(posPointA2.m_north_m);
        /* Second line segment */
        double dX3(posPointB1.m_east_m);
        double dY3(posPointB1.m_north_m);
        double dX4(posPointB2.m_east_m);
        double dY4(posPointB2.m_north_m);
        /* Output value: point of intersection */
        double dX(0);
        double dY(0);

        double a1, a2, b1, b2, c1, c2; /* Coefficients of line eqns. */
        double r1, r2, r3, r4; /* 'Sign' values */
        double denom, offset, num; /* Intermediate values */

        /* Compute a1, b1, c1, where line joining points 1 and 2 is "a1 x  +  b1 y  +  c1  =  0".*/
        a1 = dY2 - dY1;
        b1 = dX1 - dX2;
        c1 = dX2 * dY1 - dX1 * dY2;

        /* Compute r3 and r4.*/
        r3 = a1 * dX3 + b1 * dY3 + c1;
        r4 = a1 * dX4 + b1 * dY4 + c1;

        /* Check signs of r3 and r4.  If both point 3 and point 4 lie on
         * same side of line 1, the line segments do not intersect.*/
        if (r3 != 0 && r4 != 0 && SAME_SIGNS(r3, r4))
        {
            //return ( DONT_INTERSECT );
        }
        else
        {
            /* Compute a2, b2, c2 */
            a2 = dY4 - dY3;
            b2 = dX3 - dX4;
            c2 = dX4 * dY3 - dX3 * dY4;

            /* Compute r1 and r2 */
            r1 = a2 * dX1 + b2 * dY1 + c2;
            r2 = a2 * dX2 + b2 * dY2 + c2;

            /* Check signs of r1 and r2.  If both point 1 and point 2 lie
             * on same side of second line segment, the line segments do
             * not intersect.*/
            if (r1 != 0 && r2 != 0 && SAME_SIGNS(r1, r2)){/*return ( DONT_INTERSECT );*/}
            else
            {
                /* Line segments intersect: compute intersection point. */
                denom = a1 * b2 - a2 * b1;
                if (denom == 0){/*return ( COLLINEAR );*/}
                else
                {
                    offset = denom < 0 ? - denom / 2 : denom / 2;

                    /* The denom/2 is to get rounding instead of truncating.  It
                     * is added or subtracted to the numerator, depending upon the
                     * sign of the numerator.
                     */

                    num = b1 * c2 - b2 * c1;
                    dX = (num < 0 ? num - offset : num + offset) / denom;

                    num = a2 * c1 - a1 * c2;
                    dY = (num < 0 ? num - offset : num + offset) / denom;

                    //return ( DO_INTERSECT );
                    posIntersectionPoint.m_east_m = dX;
                    posIntersectionPoint.m_north_m = dY;
                    bReturn = true;
                    /* lines_intersect */
                } //if ( denom == 0 )
            }       //if (r1 != 0 && r2 != 0 && SAME_SIGNS(r1, r2)){/*return ( DONT_INTERSECT );*/}
        } //if ( r3 != 0 && r4 != 0 && SAME_SIGNS( r3, r4 ))
        return (bReturn);
    };
    
    
    bool CEdge::bIntersection(const V_POSITION_t& cVertexContainer, const CPosition& posThatB1, const CPosition& posThatB2,
                                        const n_Const::PlanCost_t& i32IndexA,const n_Const::PlanCost_t& i32IndexB,CPosition& posIntersectionPoint)
    {
        bool bReturn(false);    //i.e. no intersection
        //check for intersection of segments
        //copy intersection point to "posIntersectionPoint"

        //if the segments have a vertex in common, then do they intersect!
        if((first==i32IndexA)|| (first==i32IndexB)||
            (second==i32IndexA)|| (second==i32IndexB))
        {
#undef DO_INTERSECT_AT_VERTEX
#ifdef DO_INTERSECT_AT_VERTEX
                    bReturn = true;
#else   //#ifdef DO_INTERSECT_AT_VERTEX
                    bReturn = false;
#endif   //#ifdef DO_INTERSECT_AT_VERTEX
        }
        else
        {
                    bReturn = bFindIntersection(cVertexContainer[static_cast<int64_t>(first)],cVertexContainer[static_cast<int64_t>(second)],
                                                                                                                posThatB1,posThatB2,posIntersectionPoint);
        }        //if((first==eThat.first)||
        return(bReturn);
    };

    bool CEdge::bIntersection(const V_POSITION_t& cVertexContainer,const CEdge& eThat,CPosition& posIntersectionPoint)
    {
        bool bReturn(false);    //i.e. no intersection
        //check for intersection of segments
        //copy intersection point to "posIntersectionPoint"

        //if the segments have a vertex in common, then they do not intersect!
        if((first==eThat.first)||
            (first==eThat.second)||
            (second==eThat.first)||
            (second==eThat.second))
        {
#ifdef DO_INTERSECT_AT_VERTEX
                    bReturn = true;
#else   //#ifdef DO_INTERSECT_AT_VERTEX
                    bReturn = false;
#endif   //#ifdef DO_INTERSECT_AT_VERTEX
        }
        else
        {
                    bReturn = bFindIntersection(cVertexContainer[static_cast<int64_t>(first)],cVertexContainer[static_cast<int64_t>(second)],
                                                            cVertexContainer[static_cast<int64_t>(eThat.first)],cVertexContainer[static_cast<int64_t>(eThat.second)],posIntersectionPoint);
        }        //if((first==eThat.first)||
        return(bReturn);
    };

    bool CEdge::bIntersection(const V_POSITON_ID_t& cVertexContainer,const CEdge& eThat,CPosition& posIntersectionPoint)
    {
        bool bReturn(false);    //i.e. no intersection
        //check for intersection of segments
        //copy intersection point to "posIntersectionPoint"

        //if the segments have a vertex in common, then they do not intersect!
        if((first==eThat.first)||
            (first==eThat.second)||
            (second==eThat.first)||
            (second==eThat.second))
        {
#ifdef DO_INTERSECT_AT_VERTEX
                    bReturn = true;
#else   //#ifdef DO_INTERSECT_AT_VERTEX
                    bReturn = false;
#endif   //#ifdef DO_INTERSECT_AT_VERTEX
        }
        else
        {
                    bReturn = bFindIntersection(cVertexContainer[static_cast<int64_t>(first)],cVertexContainer[static_cast<int64_t>(second)],
                                                            cVertexContainer[static_cast<int64_t>(eThat.first)],cVertexContainer[static_cast<int64_t>(eThat.second)],posIntersectionPoint);
        }        //if((first==eThat.first)||
        return(bReturn);
    };
    
    
    
    
    
    
};      //namespace n_FrameworkLib
