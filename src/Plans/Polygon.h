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
// Polygon.h: interface for the CPolygon class.
//
// This is a list of polygon verticies.
//    ASSUMPTIONS:
//        1. the polygon is closed
//        2. adjacent verticies share an edge
//        3. the first and last verticies share an edge
//
//
//
//////////////////////////////////////////////////////////////////////

#if !defined(AFX_Polygon_H__CE91A42E_2AFF_46F1_9D41_15AD11E2A6D6__INCLUDED_)
#define AFX_Polygon_H__CE91A42E_2AFF_46F1_9D41_15AD11E2A6D6__INCLUDED_

#if _MSC_VER > 1000
#pragma once
#endif // _MSC_VER > 1000

//#include "GlobalDefines.h"    //V_INT_t

#include "Position.h"
#include "Edge.h"
#include "CGrid.h"
#include "visilibity.h"     //polygon expansion


#include "afrl/cmasi/AbstractZone.h"
#

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <Windows.h>
#endif//_WIN32

#include "boost/dynamic_bitset.hpp"    //use  id bits for local ID
#include <unordered_map>
#include <list>
#include <utility>    //pair
#include <map>
#include <vector>
#include <sstream>

#if (defined(__APPLE__) && defined(__MACH__))
#define OSX
#endif

#define MAX_NUMBER_POLYGONS (128)    //for effeciency use a multiple of sizeof(unsigned long)

namespace n_FrameworkLib
{

class CBoundary;
typedef std::shared_ptr<CBoundary> PTR_BOUNDARY_t;
typedef std::map<uint64_t,PTR_BOUNDARY_t> M_UI64_PTR_BOUNDARY_t;    


class CBoundary: public afrl::cmasi::AbstractZone
{
public:    //enumerations


public:    //typedefs
    typedef boost::dynamic_bitset<> DYNAMIC_BITSET_t;

public:    //constructors/destructors
    CBoundary(const uint32_t& uiLocalID,const bool& bKeepInZone,const V_POSITION_t& vposBoundaryPoints_m,const afrl::cmasi::AbstractZone& cmasiAbstractZone)
        :
        afrl::cmasi::AbstractZone(cmasiAbstractZone),
		m_uiLocalID(uiLocalID),
        m_bKeepInZone(bKeepInZone),
        m_vposBoundaryPoints_m(vposBoundaryPoints_m)
    {};

    ~CBoundary(){};

    CBoundary(const CBoundary& rhs)
        :
        afrl::cmasi::AbstractZone(rhs)
    {
        CopySimpleValues(rhs);
    };

    void operator =(const CBoundary& rhs)
    {
        afrl::cmasi::AbstractZone::operator =(rhs);
        CopySimpleValues(rhs);
    }

    void CopySimpleValues(const CBoundary& rhs)
    {
        bGetKeepInZone() = rhs.bGetKeepInZone();
        uiGetLocalID() = rhs.uiGetLocalID();
        vposGetBoundaryPoints_m() = rhs.vposGetBoundaryPoints_m();
    };
    

public:    //accessors
    uint32_t& uiGetLocalID(){return(m_uiLocalID);};
    const uint32_t& uiGetLocalID()const{return(m_uiLocalID);};

    bool& bGetKeepInZone(){return(m_bKeepInZone);};
    const bool& bGetKeepInZone()const{return(m_bKeepInZone);};

    V_POSITION_t& vposGetBoundaryPoints_m(){return(m_vposBoundaryPoints_m);};
    const V_POSITION_t& vposGetBoundaryPoints_m()const{return(m_vposBoundaryPoints_m);};

protected:    //storage
    uint32_t m_uiLocalID;
    bool m_bKeepInZone;
    V_POSITION_t m_vposBoundaryPoints_m;        //used to store the converted/calculated boundary points
};
    


class CPolygonType
{
public:    //enumerations
    enum enPolygonType
    {
        polytypNoFlyThreat,
        polytypNoFlyTerrain,
        polytypBoundaryOutside,
        polytypNumber
    };

public:    //constructors/destructors
    CPolygonType(const enPolygonType& polytypType=polytypNoFlyThreat)
        :m_bShrinkable(true),m_bExpandable(true),m_bKeepIn(true)
    {
        InitializeType(polytypType);
    };

    CPolygonType(const CPolygonType& rhs)
    {
        bGetShrinkable() = rhs.bGetShrinkable();
        bGetExpandable() = rhs.bGetExpandable();
        bGetKeepIn() = rhs.bGetKeepIn();
    };

    void operator =(const CPolygonType& rhs)
    {
        bGetShrinkable() = rhs.bGetShrinkable();
        bGetExpandable() = rhs.bGetExpandable();
        bGetKeepIn() = rhs.bGetKeepIn();
    };


public:    //methods/functions
    void InitializeType(const enPolygonType& polytypType)
    {
        switch(polytypType)
        {
        default:
        case polytypNoFlyThreat:
            bGetShrinkable() = true;
            bGetExpandable() = true;
            bGetKeepIn() = false;
            break;
        case polytypNoFlyTerrain:
            bGetShrinkable() = false;
            bGetExpandable() = true;
            bGetKeepIn() = false;
            break;
        case polytypBoundaryOutside:
            bGetShrinkable() = true;
            bGetExpandable() = false;
            bGetKeepIn() = true;
            break;
        }
    };

public:    //accessors
    bool& bGetShrinkable(){return(m_bShrinkable);};
    const bool& bGetShrinkable()const{return(m_bShrinkable);};

    bool& bGetExpandable(){return(m_bExpandable);};
    const bool& bGetExpandable()const{return(m_bExpandable);};

    bool& bGetKeepIn(){return(m_bKeepIn);};
    const bool& bGetKeepIn()const{return(m_bKeepIn);};

protected:    //storage
    bool m_bShrinkable;
    bool m_bExpandable;
    bool m_bKeepIn;        //is this a boundary (KeepIn) or obsticle (~KeepIn)
};


class CPolygon
{
public:    //struct
    struct rasVertex3d
    { 
        double x; 
        double y;
        double z;

        rasVertex3d()
        {
            x = 0.0;
            y = 0.0;
            z = 0.0;
        };
        rasVertex3d(const rasVertex3d& rhs)
        {
            x = rhs.x;
            y = rhs.y;
            z = rhs.z;
        };
        rasVertex3d(double x_in,double y_in,double z_in=0.0)
        {
            x = x_in;
            y = y_in;
            z = z_in;
        };
        void operator=(const rasVertex3d& rhs)
        {
            x = rhs.x;
            y = rhs.y;
            z = rhs.z;
        };
    };

public:    //typedefs
    typedef CEdge::V_EDGE_t V_EDGE_t;
    typedef CEdge::V_EDGE_IT_t V_EDGE_IT_t;
    typedef CEdge::V_EDGE_CONST_IT_t V_EDGE_CONST_IT_t;

    typedef CPolygonType::enPolygonType enPolygonType;

    typedef vector<CPolygon> V_POLYGON_t;
    typedef vector<CPolygon>::iterator V_POLYGON_IT_t;
    typedef vector<CPolygon>::const_iterator V_POLYGON_CONST_IT_t;

    typedef pair <int,V_POLYGON_IT_t> PAIR_INT_ITPOLYGON_t;
    typedef multimap<int,V_POLYGON_IT_t> MMAP_INT_ITPOLYGON_t;
    typedef multimap<int,V_POLYGON_IT_t>::iterator MMAP_INT_ITPOLYGON_IT_t;
    typedef multimap<int,V_POLYGON_IT_t>::const_iterator MMAP_INT_ITPOLYGON_CONST_IT_t;

    typedef boost::dynamic_bitset<> DYNAMIC_BITSET_t;

public:    //enumerations
    enum enCentroidType
    {
        cntrdMeanNorthMeanEast,
        cntrdNumberCentroidTypes
    };

    enum enError
    {
        errNoError,
        errUnknownError,
        errProperForm,
        errConcavity,
        errCentroid,
        errExpand,
        errMerge,
        errNumber
    };

    enum enPolygonClassification
    {
        plyclsNotConvex,
        plyclsNotConvexDegenerate,
        plyclsConvexDegenerate,
        plyclsConvexCCW,
        plyclsConvexCW
    };


    enum TESTS
    {
        ANGLE,
        BARYCENTRIC,
        CROSSINGS,
        GRID,
        CROSSMULT,
        PLANE,
        SPACKMAN,
        TRAPEZOID,
        WEILER
    };

public:    //constructors/destructors
    CPolygon(const int& iID,const enPolygonType& polytypType=CPolygonType::polytypNoFlyThreat)
        :m_iID(iID),
	    m_bValidCentroid(false),
	    m_plytypPolygonType(polytypType),
	    m_plyclsPolygonClassification(plyclsConvexCW),
	    m_dPolygonExpansionDistance(0.0),
	    m_dynbsLocalID(MAX_NUMBER_POLYGONS),
		SelectedTest(GRID),
		GridUpdateNeeded(true),
		BBUpdateNeeded(true),
		GridPtr(0)
    {
        posminBBoxPoint.m_north_m=(0);
        posminBBoxPoint.m_east_m=(0);
        posminBBoxPoint.m_altitude_m=(0);
        posmaxBBoxPoint.m_north_m=(0);
        posmaxBBoxPoint.m_east_m=(0);
        posmaxBBoxPoint.m_altitude_m=(0);

    };



    ~CPolygon()
    {
        if(GridPtr)
        {
            delete GridPtr;
        }
        GridPtr = 0;
    };

    CPolygon(const CPolygon& rhs)
        :m_dynbsLocalID(MAX_NUMBER_POLYGONS)
    {
        operator =(rhs);
    };

    void operator =(const CPolygon& rhs)
    {
        iGetID() = rhs.iGetID();
        viGetVerticies() = rhs.viGetVerticies();
        posGetCentroid() = rhs.posGetCentroid();
        bGetValidCentroid() = rhs.bGetValidCentroid();
        plytypGetPolygonType() = rhs.plytypGetPolygonType();
        plyclsGetPolygonClassification() = rhs.plyclsGetPolygonClassification();
        veGetPolygonEdges() = rhs.veGetPolygonEdges();
        veGetExtraVisibleEdges() = rhs.veGetExtraVisibleEdges();
        dGetPolygonExpansionDistance() = rhs.dGetPolygonExpansionDistance();
        GridPtr = 0;
        GridUpdateNeeded = true;
        BBUpdateNeeded = true;
        dynbsGetLocalID() = rhs.dynbsGetLocalID();
    };

public:    //methods/functions

    void StreamPolygonPython(ostream &os, V_POSITION_t& vposVerticiesBase)
    {
        for (CEdge::V_EDGE_CONST_IT_t itEdge = veGetPolygonEdges().begin(); itEdge != veGetPolygonEdges().end(); itEdge++)
        {
            //os << "[";
            os << vposVerticiesBase[static_cast<unsigned int>(itEdge->first)];
            os << ",";
            os << vposVerticiesBase[static_cast<unsigned int>(itEdge->second)];
            os << ",";
            os << itEdge->iGetLength();
            os << ",";
            os << itEdge->first;
            os << ",";
            os << itEdge->second;
            os << ",";
            os << static_cast<int>(plytypGetPolygonType().bGetKeepIn());
            //os << "]" << std::endl;
            os << std::endl;
        }
    };

    void StreamPolygonMatlab(ostream &os, V_POSITION_t& vposVerticiesBase)
    {
        for (CEdge::V_EDGE_CONST_IT_t itEdge = veGetPolygonEdges().begin(); itEdge != veGetPolygonEdges().end(); itEdge++)
        {
            //os << "[";
            os << vposVerticiesBase[static_cast<unsigned int>(itEdge->first)];
            os << ",";
            os << vposVerticiesBase[static_cast<unsigned int>(itEdge->second)];
            os << ",";
            os << itEdge->iGetLength();
            os << ",";
            os << itEdge->first;
            os << ",";
            os << itEdge->second;
            os << ",";
            os << static_cast<int>(plytypGetPolygonType().bGetKeepIn());
            //os << "]" << std::endl;
            os << std::endl;
        }
    };

    void StreamPolygonCPP(ostream &os, V_POSITION_t& vposVerticiesBase)
    {
        os << "//add polygon ID:[" << iGetID() <<"]" << endl;
        os << "vposVerticies.clear();" << endl;
        os << "iID = " << iGetID() << ";" << endl;
        for(CEdge::V_EDGE_CONST_IT_t itEdge=veGetPolygonEdges().begin();itEdge!=veGetPolygonEdges().end();itEdge++)
        {
            os << "vposVerticies.push_back(CPosition(" << vposVerticiesBase[static_cast<unsigned int>(itEdge->first)].m_north_m 
                << "," 
                << vposVerticiesBase[static_cast<unsigned int>(itEdge->first)].m_east_m << "));" << endl;
        }
        os << "errAddPolygon = visibilityGraph.errAddPolygon(iID,vposVerticies.begin(),vposVerticies.end());" << endl;
        os << "visibilityGraph.vplygnGetPolygons().back().plytypGetPolygonType().bGetKeepIn() = false;" << endl << endl;
    };

    void ResetPolygon()
    {
        // removes everything but the verticies
        bGetValidCentroid() = false;
        veGetPolygonEdges().clear();
        veGetExtraVisibleEdges().clear();
        mmapiitGetSortedDistancesToOtherPolygons().clear();
    }
    
    enError errFinalizePolygon(V_POSITION_t& vposVertexContainer,
                                const enCentroidType& cntrdType=cntrdMeanNorthMeanEast)
    {
        enError errReturn(errNoError);

        ResetPolygon();

        errReturn = errCalculateCentroid(vposVertexContainer,cntrdType);
        errReturn = errCheckForConcavity(vposVertexContainer);

        //construct polygon edges
        veGetPolygonEdges().clear();
        auto itVertex1 = m_viVerticies.begin();
        auto itVertex2 = itVertex1 + 1;
        for(;itVertex1!=m_viVerticies.end();itVertex1++,itVertex2++)
        {
            if(itVertex2 == m_viVerticies.end())
            {
                itVertex2 = m_viVerticies.begin();
            }
            int iDistance = static_cast<int>(vposVertexContainer[*itVertex1].relativeDistance2D_m(vposVertexContainer[*itVertex2]));
            CEdge eEdge(*itVertex1,*itVertex2,iDistance);
            veGetPolygonEdges().push_back(eEdge);
        }

        return(errReturn);
    };


    enError errCalculateCentroid(V_POSITION_t& vposVertexContainer,
        const enCentroidType& cntrdType=cntrdMeanNorthMeanEast)
    {
        enError errReturn(errNoError);

        switch(cntrdType)
        {
        default:
        case cntrdMeanNorthMeanEast:
            {
                double dTotalNorth(0.0);
                double dTotalEast(0.0);
                for(auto itVertex=m_viVerticies.begin();itVertex!=m_viVerticies.end();itVertex++)
                {
                    dTotalNorth += vposVertexContainer[*itVertex].m_north_m;
                    dTotalEast += vposVertexContainer[*itVertex].m_north_m;
                }
                assert(!viGetVerticies().empty());
                posGetCentroid().m_north_m = dTotalNorth/viGetVerticies().size();
                posGetCentroid().m_east_m = dTotalEast/viGetVerticies().size();
                bGetValidCentroid() = true;
            }
            break;
        }
        return(errReturn);
    };

    enError errCalculateDistanceToOtherPolygons(V_POLYGON_IT_t& itPolygonBegin,V_POLYGON_IT_t& itPolygonEnd)
    {
        // assumes that the iterators to the polygons will not change, i.e. I'm storing iterators!!
        enError errReturn(errNoError);

        for(V_POLYGON_IT_t itPolygon=itPolygonBegin;itPolygon!=itPolygonEnd;itPolygon++)
        {
            if(itPolygon->bGetValidCentroid())
            {
                //need to have a list of all polygons, including this one. (used to check for edge intersections)
                int iDistance(0);
                if(iGetID()!=itPolygon->iGetID())
                {
                    iDistance = static_cast<int>(posGetCentroid().relativeDistance2D_m(itPolygon->posGetCentroid()));
                }
                mmapiitGetSortedDistancesToOtherPolygons().insert(PAIR_INT_ITPOLYGON_t(iDistance,itPolygon));
            }
            else
            {
                errReturn = errCentroid;
                break;
            }
        }

        return(errReturn);
    };

    /*
    * C code from the article
    * "Testing the Convexity of a Polygon"
    * by Peter Schorn and Frederick Fisher,
    *    (schorn@inf.ethz.ch, fred@kpc.com)
    * in "Graphics Gems IV", Academic Press, 1994
    */

    /* Program to Classify a Polygon's Shape */

    struct Point2d
    { 
        double x; 
        double y;

        Point2d()
        {
            x = 0.0;
            y = 0.0;
        };
        Point2d(const CPosition& rhs)
        {
            x = rhs.m_north_m;
            y = rhs.m_east_m;
        };
        void operator =(const CPosition& rhs)
        {
            x = rhs.m_north_m;
            y = rhs.m_east_m;
        };
        Point2d(const Point2d& rhs)
        {
            x = rhs.x;
            y = rhs.y;
        };
        void operator =(const Point2d& rhs)
        {
            x = rhs.x;
            y = rhs.y;
        };
    } ;

    int WhichSide(Point2d& p,Point2d& q,Point2d& r)        /* Given a directed line pq, determine    */
        //Point2d          p, q, r;        /* whether qr turns CW or CCW.        */
    {
        double result;
        result = (p.x - q.x) * (q.y - r.y) - (p.y - q.y) * (q.x - r.x);
        if (result < 0) return -1;    /* q lies to the left  (qr turns CW).    */
        if (result > 0) return  1;    /* q lies to the right (qr turns CCW).    */
        return 0;            /* q lies on the line from p to r.    */
    };

    int Compare(Point2d& p,Point2d& q)        /* Lexicographic comparison of p and q    */
        //Point2d        p, q;
    {
        if (p.x < q.x) return -1;    /* p is less than q.            */
        if (p.x > q.x) return  1;    /* p is greater than q.            */
        if (p.y < q.y) return -1;    /* p is less than q.            */
        if (p.y > q.y) return  1;    /* p is greater than q.            */
        return 0;            /* p is equal to q.            */
    };

    /* CheckTriple tests three consecutive points for change of direction
    * and for orientation.
    */
/*
    #define CheckTriple                            \
        if ( (thisDir = Compare(second, third)) == -curDir )        \
        ++dirChanges;                        \
        curDir = thisDir;                        \
        if ( thisSign = WhichSide(first, second, third) ) {        \
        if ( angleSign == -thisSign )                \
        return plyclsNotConvex;                    \
        angleSign = thisSign;                    \
        }                                \
        first = second; second = third;
*/






    bool bCheckForIntersection(V_POSITION_t& vposVertexContainer,const CEdge& eThatEdge)
    {
        bool bIntersectionFound(false);

        for(V_EDGE_IT_t itEdge=veGetPolygonEdges().begin();itEdge!=veGetPolygonEdges().end();itEdge++)
        {
            if(itEdge->bIntersection(vposVertexContainer,eThatEdge))
            {
                bIntersectionFound = true;
                break;
            }
        }
        return(bIntersectionFound);
    };

    void findIntersections(const std::vector<CPosition>& vposVertexContainer,const CPosition& posThatB1, const CPosition& posThatB2 ,std::vector<CPosition>& intersectionPoints)
    {
            for(V_EDGE_IT_t itEdge=veGetPolygonEdges().begin();itEdge!=veGetPolygonEdges().end();itEdge++)
            {
                CPosition intersectionPoint;
                if(itEdge->bIntersection(vposVertexContainer,posThatB1,posThatB2,-1,-1,intersectionPoint))
                {
                    intersectionPoints.push_back(intersectionPoint);
                }
            }
    };


    enError errCheckForConcavity(V_POSITION_t& vposVerticies);
    enError errFindSelfVisibleEdges(V_POSITION_t& vposVertexContainer);
    enError errFindVisibleEdges(V_POSITION_t& vposVertexContainer,const V_POLYGON_CONST_IT_t& itPolygonThat,V_EDGE_t& veEdgesVisible);
    enError errAddExtraVisibleEdges(V_POSITION_t& vposVertexContainer,const V_POLYGON_CONST_IT_t& itPolygonThat,V_EDGE_t& veEdgesVisible);



public:    //accessors
    int& iGetID(){return(m_iID);};
    const int& iGetID()const{return(m_iID);};

    std::vector<int32_t>& viGetVerticies(){return(m_viVerticies);};
    const std::vector<int32_t>& viGetVerticies()const{return(m_viVerticies);};

    CPosition& posGetCentroid(){return(m_posCentroid);};
    const CPosition& posGetCentroid()const{return(m_posCentroid);};

    bool& bGetValidCentroid(){return(m_bValidCentroid);};
    const bool& bGetValidCentroid()const{return(m_bValidCentroid);};

    CPolygonType& plytypGetPolygonType(){return(m_plytypPolygonType);};
    const CPolygonType& plytypGetPolygonType()const{return(m_plytypPolygonType);};

    enPolygonClassification& plyclsGetPolygonClassification(){return(m_plyclsPolygonClassification);};
    const enPolygonClassification& plyclsGetPolygonClassification()const{return(m_plyclsPolygonClassification);};

    V_EDGE_t& veGetPolygonEdges(){return(m_vePolygonEdges);};
    const V_EDGE_t& veGetPolygonEdges()const{return(m_vePolygonEdges);};

    V_EDGE_t& veGetExtraVisibleEdges(){return(m_veExtraVisibleEdges);};
    const V_EDGE_t& veGetExtraVisibleEdges()const{return(m_veExtraVisibleEdges);};

    MMAP_INT_ITPOLYGON_t& mmapiitGetSortedDistancesToOtherPolygons(){return(m_mmapiitSortedDistancesToOtherPolygons);};
    const MMAP_INT_ITPOLYGON_t& mmapiitGetSortedDistancesToOtherPolygons()const{return(m_mmapiitSortedDistancesToOtherPolygons);};

    double& dGetPolygonExpansionDistance(){return(m_dPolygonExpansionDistance);};
    const double& dGetPolygonExpansionDistance()const{return(m_dPolygonExpansionDistance);};

    DYNAMIC_BITSET_t& dynbsGetLocalID(){return(m_dynbsLocalID);};
    const DYNAMIC_BITSET_t& dynbsGetLocalID()const{return(m_dynbsLocalID);};

public:    //storage
    std::vector<int32_t> m_viVerticies;
    
protected:    //storage
    int m_iID;    //each polygon must have a unique ID number
    CPosition m_posCentroid;
    bool m_bValidCentroid;

    CPolygonType m_plytypPolygonType;
    enPolygonClassification m_plyclsPolygonClassification;        //does the polygon have a concavity?

    //storage for polygon edges
    V_EDGE_t m_vePolygonEdges;
    //        - if polygon is concave, then need to add extra "visible" edges, paying attention to the "KeepIn"/"~KeepIn" property
    V_EDGE_t m_veExtraVisibleEdges;

    //TODO:: need a container that sorts polygons based on distance between centroids and saves polygon iterators.
    MMAP_INT_ITPOLYGON_t m_mmapiitSortedDistancesToOtherPolygons;

    double m_dPolygonExpansionDistance;

    DYNAMIC_BITSET_t m_dynbsLocalID;

    /************************************************
    *                Accessor Functions              *
    *************************************************/
    //VPoints &GetPolygon() {    return(*VPoints_ptr); };
    //const VPoints &GetPolygon() const {    return (*VPoints_ptr); };

    double GetNumPoints(){return(viGetVerticies().size());};

    enum TESTS& GetTest() { return(SelectedTest); };
    const enum TESTS& GetTest() const { return (SelectedTest); };

    void getBBox(CPosition &minBB, CPosition &maxBB) { minBB = posminBBoxPoint ; maxBB = posmaxBBoxPoint; };

    CPosition& posGetMaxBBoxPoint(){return(posmaxBBoxPoint);};    //Point maxBBoxPoint;
    CPosition& posGetMinBBoxPoint(){return(posminBBoxPoint);};    //Point maxBBoxPoint;
    bool& bGetBBUpdateNeeded(){return(BBUpdateNeeded);};    
    bool& bGetGridUpdateNeeded(){return(GridUpdateNeeded);};    

    /*************************************************
    *                Private Member Variables         *
    *************************************************/
private:
    enum TESTS SelectedTest;
    CPosition posmaxBBoxPoint;    //Point maxBBoxPoint;
    CPosition posminBBoxPoint;    //Point minBBoxPoint;
    bool bInPolygon;
    bool GridUpdateNeeded;
    bool BBUpdateNeeded;

    //// "Edge" equation is really line: Ax +By + C = 0 using 2 point formula
    //// (y-y1) / (x - x1) = (y2 - y1) / (x2 - x1)
    //struct Edge { double A; double B; double C; };


    CGrid *GridPtr;                    // want as pointer because may not always exist

    /************************************************
    *                Private Member Functions        *
    *************************************************/
private:
    void GridTest(const double x, const double y,const double z,V_POSITION_t& vposVertexContainer,stringstream &sstrErrorMessage);
    // copy constructor - make unusable to prevent bad things from happening
    //CPolygon(const CPolygon& Polygon) {};
    //// assignment operator - make unusable to prevent bad things from happening
    //CPolygon & operator = (const CPolygon& Polygon) {};


    /************************************************
    *                Public Member Functions            *
    *************************************************/
public:    
    bool InPolygon(const double x, const double y, 
        const double z,V_POSITION_t& vposVertexContainer, stringstream &sstrErrorMessage);

    void FindPolygonBoundingBox(V_POSITION_t& vposVertexContainer,stringstream &sstrErrorMessage);

    bool PointInBoundingBox(const double x, const double y, 
        const double z, stringstream &sstrErrorMessage); 

};


ostream &operator << (ostream &os,const CPolygon& polyRhs);

};      ///namespace n_FrameworkLib

#endif // !defined(AFX_Polygon_H__CE91A42E_2AFF_46F1_9D41_15AD11E2A6D6__INCLUDED_)
