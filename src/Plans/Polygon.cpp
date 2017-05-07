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
//    CPolygon class.
//
//////////////////////////////////////////////////////////////////////
//    Date    Name    Ver     Modification
//    2/9/05    afj     1.0     created
//
//////////////////////////////////////////////////////////////////////


//#pragma warning(disable:4786)
#define DEBUG_FLAG 0
#define METHOD_DEBUG 0
#include "Polygon.h"
#include <iostream>
#include <sstream>
#include <math.h>
//#include "GlobalDefines.h"
#include "CGrid.h"

using namespace std;

namespace n_FrameworkLib
{

/****************************************************/
/*                Tests if Data Point in Polygon        */
/****************************************************/    
bool CPolygon::InPolygon(double x, double y, double z,V_POSITION_t& vposVertexContainer, stringstream &sstrErrorMessage ) 
{
#if DEBUG_FLAG==1
    cout << "CPolygon In Polygon Method\n";
#endif
    // reinitialize to false
    bInPolygon = false;

    if (!viGetVerticies().empty())         // skip if null pointer no data points
    {        
#if DEBUG_FLAG==1
        cout << "InPolygon:: BBUpdateNeeded[" <<  BBUpdateNeeded << "]\n";
#endif
        if (BBUpdateNeeded) {
            FindPolygonBoundingBox(vposVertexContainer,sstrErrorMessage);
            BBUpdateNeeded = false;
        }
        //PointInBoundingBox(x,y,z,sstrErrorMessage);
        bInPolygon = PointInBoundingBox(x,y,z,sstrErrorMessage);

        if (bInPolygon) 
        {
#if DEBUG_FLAG==1
            cout << "InPolygon:: bInPolygon[" <<  bInPolygon << "]\n";
#endif
#ifndef STEVETEST
            SelectedTest = GRID;
#endif    //STEVETEST
            switch (SelectedTest) 
            {
            case GRID:
                GridTest(x,y,z,vposVertexContainer,sstrErrorMessage);
                break;
            default:                    //NEVER EVER SHOULD END UP HERE
                sstrErrorMessage << "ERROR!  Invalid Test in Polygon Algorithm specified.\n";
                cout << sstrErrorMessage.str();
                //mexErrTxt(sstrErrorMessage.str().c_str());        
            }

        }
    }
    return bInPolygon;
}



/****************************************************/
/*        Is it in Polygon using Grid Test            */
/****************************************************/
void CPolygon::GridTest(double x, double y, double z,V_POSITION_t& vposVertexContainer,stringstream &sstrErrorMessage) 
{
#if DEBUG_FLAG==1
    cout << "CPolygon GridTest() Method\n";
#endif

    if ((!GridPtr) || (GridUpdateNeeded)) {
        if (GridPtr)
            delete GridPtr;
#ifdef STEVETEST
        GridPtr = new CGrid(viGetVerticies(),vposVertexContainer, 1, 1, posminBBoxPoint,posmaxBBoxPoint, sstrErrorMessage);
#else    //STEVETEST
        GridPtr = new CGrid(viGetVerticies(),vposVertexContainer, 5, 5, posminBBoxPoint,posmaxBBoxPoint, sstrErrorMessage);
#endif    //STEVETEST
        GridUpdateNeeded = false;

    }

    bInPolygon = GridPtr->InPolygon(x, y, z, posminBBoxPoint, sstrErrorMessage);

}



/****************************************************/
/*        Is it in Polygon using Grid Test            */
/****************************************************/
inline bool CPolygon::PointInBoundingBox(double x, double y, double z, stringstream &sstrErrorMessage) {
#if DEBUG_FLAG==1
    cout << "CPolygon PointInBoundingBox() Method\n";
#endif

    return (( x >= posminBBoxPoint.m_north_m ) && ( x <= posmaxBBoxPoint.m_north_m ) && ( y >= posminBBoxPoint.m_east_m ) && ( y <= posmaxBBoxPoint.m_east_m ) );
} 

/****************************************************/
/*        Is it in Polygon using Grid Test            */
/****************************************************/
void CPolygon::FindPolygonBoundingBox(V_POSITION_t& vposVertexContainer,stringstream &sstrErrorMessage) 
{
#if DEBUG_FLAG==1
    cout << "CPolygon FindPolygonBoundingBox() Method\n";
#endif

    double curX = 0,curY = 0, EPSILON = .00001;
    BBUpdateNeeded = false;


    posminBBoxPoint = vposVertexContainer[viGetVerticies()[0]];
    posmaxBBoxPoint = vposVertexContainer[viGetVerticies()[0]];

    for (size_t szIndex=0;szIndex < viGetVerticies().size(); szIndex++ ) {
        curX = vposVertexContainer[viGetVerticies()[szIndex]].m_north_m;
        curY = vposVertexContainer[viGetVerticies()[szIndex]].m_east_m;
        if ( posminBBoxPoint.m_north_m > curX ) 
            posminBBoxPoint.m_north_m = curX;
        else if(posmaxBBoxPoint.m_north_m <= curX )
            posmaxBBoxPoint.m_north_m = curX;
        if ( posminBBoxPoint.m_east_m > curY ) 
            posminBBoxPoint.m_east_m = curY;
        else if(posmaxBBoxPoint.m_east_m <= curY )
            posmaxBBoxPoint.m_east_m = curY;
    }
    // make it just a little BIGGER
    double xdiff = posmaxBBoxPoint.m_north_m - posminBBoxPoint.m_north_m;
    double ydiff = posmaxBBoxPoint.m_east_m - posminBBoxPoint.m_east_m;

    if ( (posminBBoxPoint.m_north_m - EPSILON * xdiff ) >= posminBBoxPoint.m_north_m )
        sstrErrorMessage << "ERROR!!! - minX bbox scale problem\n";
    if ( (posminBBoxPoint.m_east_m - EPSILON * ydiff ) >= posminBBoxPoint.m_east_m )
        sstrErrorMessage << "ERROR!  - minY bbox scale problem \n";
    posminBBoxPoint.m_north_m -= EPSILON * xdiff;
    posminBBoxPoint.m_east_m -= EPSILON * ydiff;
    if ( (posmaxBBoxPoint.m_north_m + EPSILON * xdiff ) <= posmaxBBoxPoint.m_north_m )
        sstrErrorMessage << "ERROR!!! - maxX bbox scale problem\n";
    if ( (posmaxBBoxPoint.m_east_m + EPSILON * ydiff ) <= posmaxBBoxPoint.m_east_m )
        sstrErrorMessage << "ERROR!!! - minX bbox scale problem\n";
    posmaxBBoxPoint.m_north_m += EPSILON * xdiff;
    posmaxBBoxPoint.m_east_m += EPSILON * ydiff;    
}


    CPolygon::enError CPolygon::errCheckForConcavity(V_POSITION_t& vposVerticies)
    {
        enError errReturn(errNoError);

        //TODO:: need to examine all of the angle to make sure none are >pi rads
        // if polygon is concave calculate extra visible edges + lengths

        //TODO:: need to pre-calculate and store (extra) visible edges
        //        - if polygon is concave, then need to add extra "visible" edges, paying attention to the "KeepIn"/"~KeepIn" property
        //        - need to keep these edges seperate, because they are not boundarys




        /* Classify the polygon vertices on file 'f' according to: 'NotConvex'    */
        /* 'NotConvexDegenerate', 'ConvexDegenerate', 'ConvexCCW', 'ConvexCW'.    */
        //PolygonClass ClassifyPolygon()
        //{
        int thisDir(0);
        int thisSign(0);
        int angleSign(0);
        int dirChanges(0);

        //m_viVerticies.begin()
        //viGetVerticies()

        int iNumberVerticies(static_cast<int>(viGetVerticies().size()));
        int iNumberVertexPositions(static_cast<int>(viGetVerticies().size()));

        if((iNumberVerticies <=1)||(iNumberVertexPositions<iNumberVerticies))
        {
            plyclsGetPolygonClassification() = plyclsConvexDegenerate;
        }
        else
        {
            int iVertexIndex(0);
            Point2d first(vposVerticies[viGetVerticies()[iVertexIndex]]);
            Point2d saveFirst(first);
            iVertexIndex++;
            Point2d second(vposVerticies[viGetVerticies()[iVertexIndex]]);
            Point2d saveSecond(second);
            int curDir = Compare(first, second);
            Point2d third;
            while(true) 
            {
                iVertexIndex++;
                if(iVertexIndex < iNumberVerticies)
                {
                    third = vposVerticies[viGetVerticies()[iVertexIndex]];
                    //CheckTriple;
                    if ( (thisDir = Compare(second, third)) == -curDir )
                    {
                        dirChanges++;
                    }
                    curDir = thisDir;                        \
                        if ( thisSign = WhichSide(first, second, third) ) 
                        {
                            if ( angleSign == -thisSign )
                            {
                                plyclsGetPolygonClassification() = plyclsNotConvex;
                                return(errReturn);
                            }
                            angleSign = thisSign;                    \
                        }                                \
                        first = second; second = third;
                }
                else
                {
                    break;
                }
            }
            /* Must check that end of list continues back to start properly */
            if ( Compare(second, saveFirst) ) 
            {
                third = saveFirst; 
                //CheckTriple;
                if ( (thisDir = Compare(second, third)) == -curDir )
                {
                    dirChanges++;
                }
                curDir = thisDir;                        \
                    if ( thisSign = WhichSide(first, second, third) ) 
                    {
                        if ( angleSign == -thisSign )
                        {
                            plyclsGetPolygonClassification() = plyclsNotConvex;
                            return(errReturn);
                        }
                        angleSign = thisSign;                    \
                    }                                \
                    first = second; second = third;
            }
            third = saveSecond;     
            //CheckTriple;
            if ( (thisDir = Compare(second, third)) == -curDir )
            {
                dirChanges++;
            }
            curDir = thisDir;                        \
                if ( thisSign = WhichSide(first, second, third) ) 
                {
                    if ( angleSign == -thisSign )
                    {
                        plyclsGetPolygonClassification() = plyclsNotConvex;
                        return(errReturn);
                    }
                    angleSign = thisSign;                    \
                }                                \
                first = second; second = third;

                    if ( dirChanges > 2 )
                    {
                        plyclsGetPolygonClassification() = (angleSign)?(plyclsNotConvex):(plyclsNotConvexDegenerate);
                    }
                    else if ( angleSign  > 0 )
                    {
                        plyclsGetPolygonClassification() = plyclsConvexCCW;
                    }
                    else if ( angleSign  < 0 )
                    {
                        plyclsGetPolygonClassification() = plyclsConvexCW;
                    }
                    else
                    {
                        plyclsGetPolygonClassification() = plyclsConvexDegenerate;
                    }
        }    //if(iNumberVerticies <=1)


        return(errReturn);
    };


    CPolygon::enError CPolygon::errFindSelfVisibleEdges(V_POSITION_t& vposVertexContainer)
    {
        enError errReturn(errNoError);
        if(plyclsGetPolygonClassification() == plyclsNotConvex)
        {
            // find all the unconnected visible edges on non-convex polygons
            // only need edges in one direction
            for(auto itVertex1=viGetVerticies().begin();itVertex1!=viGetVerticies().end();itVertex1++)
            {
                for(auto itVertex2=(itVertex1+1);itVertex2!=viGetVerticies().end();itVertex2++)
                {
                    CEdge edgeNew(*itVertex1,*itVertex2);
                    CEdge edgeNewReverse(*itVertex2,*itVertex1);
                    bool bExisitingEdge(false);
                    for(V_EDGE_IT_t itEdge=veGetPolygonEdges().begin();itEdge!=veGetPolygonEdges().end();itEdge++)
                    {
                        if(((*itEdge)==edgeNew)||((*itEdge)==edgeNewReverse))
                        {
                            bExisitingEdge = true;
                            break;
                        }
                    }
                    if(!bExisitingEdge)
                    {
                        bool bIntersectionFound(false);
                        double dCenterNorth_m = (vposVertexContainer[*itVertex2].m_north_m - vposVertexContainer[*itVertex1].m_north_m)*0.5 + vposVertexContainer[*itVertex1].m_north_m;
                        double dCenterEast_m = (vposVertexContainer[*itVertex2].m_east_m - vposVertexContainer[*itVertex1].m_east_m)*0.5 + vposVertexContainer[*itVertex1].m_east_m;

                        bool bInsidePolygon(false);

                        //1. check to see if the center of the edge is in the polygon, if is is then not visible
                        // 2. check new edge against all exisitng edges
                        stringstream sstrErrorMessage;
                        bInsidePolygon = InPolygon(dCenterNorth_m,dCenterEast_m,0.0,vposVertexContainer,sstrErrorMessage);
                        bool bGoodEdge(false);

                        if(bInsidePolygon == true)
                        {
                            bGoodEdge = (plytypGetPolygonType().bGetKeepIn())?(true):(false);
                        }
                        else
                        {
                            bGoodEdge = (plytypGetPolygonType().bGetKeepIn())?(false):(true);
                        }

                        if(bGoodEdge && !bCheckForIntersection(vposVertexContainer,edgeNew))
                        {
                            edgeNew.iGetLength() = static_cast<int>(vposVertexContainer[*itVertex1].relativeDistance2D_m(vposVertexContainer[*itVertex2]));
                            veGetExtraVisibleEdges().push_back(edgeNew);
                        }
                    }    //if(!bExisitingEdge)
                }
            }
        }    //if(plyclsGetPolygonClassification() == plyclsNotConvex)
        return(errReturn);
    };

CPolygon::enError CPolygon::errFindVisibleEdges(V_POSITION_t& vposVertexContainer,const V_POLYGON_CONST_IT_t& itPolygonThat,V_EDGE_t& veEdgesVisible)
    {
        enError errReturn(errNoError);

        for(auto itVertexThis=viGetVerticies().begin();itVertexThis!=viGetVerticies().end();itVertexThis++)
        {
            for(auto itVertexThat=itPolygonThat->viGetVerticies().begin();itVertexThat!=itPolygonThat->viGetVerticies().end();itVertexThat++)
            {
                //first check to make sure that the segment doesn't violate the keep-in rules of this polygon
                //1. check to see if the center of the edge is in the polygon
                bool bGoodEdge(true);

                if(plytypGetPolygonType().bGetKeepIn())
                {
                    double dCenterNorth_m = (vposVertexContainer[*itVertexThat].m_north_m - vposVertexContainer[*itVertexThis].m_north_m)*0.5 + vposVertexContainer[*itVertexThis].m_north_m;
                    double dCenterEast_m = (vposVertexContainer[*itVertexThat].m_east_m - vposVertexContainer[*itVertexThis].m_east_m)*0.5 + vposVertexContainer[*itVertexThis].m_east_m;

                    bool bInsidePolygon(false);

                    stringstream sstrErrorMessage;
                    bInsidePolygon = InPolygon(dCenterNorth_m,dCenterEast_m,0.0,vposVertexContainer,sstrErrorMessage);

                    if(bInsidePolygon != true)
                    {
                        bGoodEdge = false;
                    }
                }        //plytypGetPolygonType().bGetKeepIn()

                // 2. check new edge against all exisitng edges
                if(bGoodEdge)
                {
                    bool bIntersectionFound(false);
                    CEdge edgeNew(*itVertexThis,*itVertexThat);
                    for(MMAP_INT_ITPOLYGON_IT_t itIntPolygon=mmapiitGetSortedDistancesToOtherPolygons().begin();
                        itIntPolygon!=mmapiitGetSortedDistancesToOtherPolygons().end();
                        itIntPolygon++)
                    {
                        V_POLYGON_IT_t itPolygonCheck = itIntPolygon->second;
                        if(itPolygonCheck->bCheckForIntersection(vposVertexContainer,edgeNew))
                        {
                            bIntersectionFound = true;
                            break;
                        }
                    }        //for(V_POLYGON_CONST_IT_t itPolygon=itPolygonAllBegin;itPolygon!=itPolygonAllEnd;itPolygon++)
                    if(!bIntersectionFound)
                    {
                        edgeNew.iGetLength() = static_cast<int>(vposVertexContainer[*itVertexThis].relativeDistance2D_m(vposVertexContainer[*itVertexThat]));
                        veEdgesVisible.push_back(edgeNew);
                    }
                }        //if(bGoodEdge)
            }        //for(auto itVertexThat=itPolygonThat->viGetVerticies().begin();itVertexThat!=itPolygonThat->viGetVerticies().end();itVertexThat++)
        }


        return(errReturn);
    };

CPolygon::enError CPolygon::errAddExtraVisibleEdges(V_POSITION_t& vposVertexContainer,const V_POLYGON_CONST_IT_t& itPolygonThat,V_EDGE_t& veEdgesVisible)
    {
        enError errReturn(errNoError);

        errReturn = errFindSelfVisibleEdges(vposVertexContainer);
        if(errReturn == errNoError)
        {

            for(V_EDGE_IT_t itEdge=veGetExtraVisibleEdges().begin();itEdge!=veGetExtraVisibleEdges().end();itEdge++)
            {
                //1. check to see if the center of the edge is in the polygon
                bool bGoodEdge(true);

                if(plytypGetPolygonType().bGetKeepIn())
                {
                    double dCenterNorth_m = (vposVertexContainer[static_cast<unsigned int>(itEdge->second)].m_north_m - vposVertexContainer[static_cast<unsigned int>(itEdge->first)].m_north_m)*0.5 + vposVertexContainer[static_cast<unsigned int>(itEdge->first)].m_north_m;
                    double dCenterEast_m = (vposVertexContainer[static_cast<unsigned int>(itEdge->second)].m_east_m - vposVertexContainer[static_cast<unsigned int>(itEdge->first)].m_east_m)*0.5 + vposVertexContainer[static_cast<unsigned int>(itEdge->first)].m_east_m;

                    bool bInsidePolygon(false);

                    stringstream sstrErrorMessage;
                    bInsidePolygon = InPolygon(dCenterNorth_m,dCenterEast_m,0.0,vposVertexContainer,sstrErrorMessage);

                    if(bInsidePolygon != true)
                    {
                        bGoodEdge = false;
                    }
                }        //plytypGetPolygonType().bGetKeepIn()
                // 2. check new edge against all exisitng edges
                if(bGoodEdge)
                {
                    bool bIntersectionFound(false);
                    for(MMAP_INT_ITPOLYGON_IT_t itIntPolygon=mmapiitGetSortedDistancesToOtherPolygons().begin();
                        itIntPolygon!=mmapiitGetSortedDistancesToOtherPolygons().end();
                        itIntPolygon++)
                    {
                        V_POLYGON_IT_t itPolygonCheck = itIntPolygon->second;
                        if(itPolygonCheck->bCheckForIntersection(vposVertexContainer,*itEdge))
                        {
                            bIntersectionFound = true;
                            break;
                        }
                    }        //for(V_POLYGON_CONST_IT_t itPolygon=itPolygonAllBegin;itPolygon!=itPolygonAllEnd;itPolygon++)
                    if(!bIntersectionFound)
                    {
                        itEdge->iGetLength() = static_cast<int>(vposVertexContainer[static_cast<unsigned int>(itEdge->first)].relativeDistance2D_m(vposVertexContainer[static_cast<unsigned int>(itEdge->second)]));
                        veEdgesVisible.push_back(*itEdge);
                    }
                }        //if(bGoodEdge)
            }
        }
        else
        {
            //TODO:: ERROR??
        }

        return(errReturn);
    };

};      //namespace n_FrameworkLib
