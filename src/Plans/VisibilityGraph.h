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
// VisibilityGraph.h: interface for the CVisibilityGraph class.
//
//
//
//
//////////////////////////////////////////////////////////////////////


#pragma once


#include "Polygon.h"

#include "VehicleBase.h"
#include "PlanningParameters.h"
#include "TrajectoryParameters.h"
#include "PathInformation.h"

#include "uxas/messages/route/GraphRegion.h"

//#include "boost/array.hpp"
#include "boost/graph/graph_traits.hpp"
#include "boost/graph/adjacency_list.hpp"
#include "boost/graph/dijkstra_shortest_paths.hpp"
#include "boost/graph/johnson_all_pairs_shortest.hpp"

#include <iostream>
#include <iomanip>
#include <fstream>
#include <ostream>
using std::ostream;
#include <complex>
using std::complex;

#include <memory>       //std::shared_ptr

namespace n_FrameworkLib
{

#define BASE_VISIBILITY_ID_OFFSET (10000000)    //add to vertex ID for a unique ID (used in visibility graph calculations)

    class CVisibilityGraph; // need a forward to define typedef
    typedef std::shared_ptr<CVisibilityGraph> PTR_VISIBILITYGRAPH_t;
    typedef std::map<uint32_t, PTR_VISIBILITYGRAPH_t> M_UI32_PTR_VISIBILITYGRAPH_t;
    //typedef std::map<uint32_t, PTR_VISIBILITYGRAPH_t>::iterator M_UI32_PTR_VISIBILITYGRAPH_IT_t;

    class CVisibilityGraph
    {
    public: //typedefs
        typedef CEdge::V_EDGE_t V_EDGE_t;
        typedef CEdge::V_EDGE_IT_t V_EDGE_IT_t;
        typedef CEdge::V_EDGE_CONST_IT_t V_EDGE_CONST_IT_t;

        typedef CPolygon::V_POLYGON_t V_POLYGON_t;
        typedef CPolygon::V_POLYGON_IT_t V_POLYGON_IT_t;
        typedef CPolygon::V_POLYGON_CONST_IT_t V_POLYGON_CONST_IT_t;

        typedef boost::adjacency_list < boost::listS, boost::vecS, boost::undirectedS, boost::no_property, boost::property < boost::edge_weight_t, int > > GRAPH_LIST_VEC_t;
        typedef boost::graph_traits <GRAPH_LIST_VEC_t>::vertex_descriptor vertex_descriptor;
        typedef boost::graph_traits <GRAPH_LIST_VEC_t>::edge_descriptor edge_descriptor;

        typedef std::vector<vertex_descriptor> V_VERTEX_DESCRIPTOR_t;
        typedef std::vector<vertex_descriptor>::iterator V_VERTEX_DESCRIPTOR_IT_t;
        typedef std::vector<vertex_descriptor>::const_iterator V_VERTEX_DESCRIPTOR_CONST_IT_t;

        typedef std::vector<V_VERTEX_DESCRIPTOR_t> V_V_VERTEX_DESCRIPTOR_t;
        typedef std::vector<V_VERTEX_DESCRIPTOR_t>::iterator V_V_VERTEX_DESCRIPTOR_IT_t;
        typedef std::vector<V_VERTEX_DESCRIPTOR_t>::const_iterator V_V_VERTEX_DESCRIPTOR_CONST_IT_t;


    typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::undirectedS, boost::no_property, boost::property<boost::edge_weight_t, int, boost::property<boost::edge_weight2_t, int> > > GRAPH_VEC_VEC_t;
        //    typedef std::pair<int,int> Edge;

        typedef std::deque<CPosition> D_POSITION_t;
        typedef std::deque<CPosition>::iterator D_POSITION_IT_t;
        typedef std::deque<CPosition>::const_iterator D_POSITION_CONST_IT_t;
        typedef std::shared_ptr<D_POSITION_t> PTR_DEQUE_POSITION_t;

        typedef complex<double> COMPLEX_D_t;

        typedef std::shared_ptr<uxas::messages::route::GraphRegion> PTR_GRAPH_REGION_t;
        typedef std::map<uint32_t, PTR_GRAPH_REGION_t> M_UI32_PTR_GRAPH_REGION_t;
        typedef std::map<uint32_t, PTR_GRAPH_REGION_t>::iterator M_UI32_PTR_GRAPH_REGION_IT_t;



    public: //enumerations

        enum enError
        {
            errNoError,
            errPolygonCreation,
            errPolygonTypeNotFound,
            errPolygonMerging,
            errVerticiesCurrent,
            errDistancesBase,
            errPathConstruction,
            errVerticiesNotFound,
            errUnknownError,
            errNumberErrors
        };

    public: //constructors/destructors
        CVisibilityGraph();
        ~CVisibilityGraph(void);

        CVisibilityGraph(const CVisibilityGraph& rhs) {
            pedglstvecGetGraph() = 0;
            operator=(rhs);
        };

        void operator=(const CVisibilityGraph& rhs) {
            vposGetVerticiesBase() = rhs.vposGetVerticiesBase();
            vplygnGetPolygons() = rhs.vplygnGetPolygons();
            veGetEdgesVisibleBase() = rhs.veGetEdgesVisibleBase();
            vviGetVertexDistancesBase() = rhs.vviGetVertexDistancesBase();
            vvvtxGetVertexParentBase() = rhs.vvvtxGetVertexParentBase();
            if (pedglstvecGetGraph()) {
                delete pedglstvecGetGraph();
            }
            pedglstvecGetGraph() = new GRAPH_LIST_VEC_t();
            edglstvecGetGraph() = edglstvecGetGraph();
            ptypeGetType() = rhs.ptypeGetType();
            iGetLengthSegmentMinimum() = rhs.iGetLengthSegmentMinimum();
        };

    public: //methods/functions
        enError errExpandAndMergePolygons(void);
        enError errBuildVisibilityGraph(void);
        enError errBuildVisibilityGraph(PTR_GRAPH_REGION_t& ptr_GraphRegion);
        enError errBuildVisibilityGraphWithOsm(const string& osmFile);
        

        bool isFindPath(std::shared_ptr<CPathInformation>& pathInformation);
#ifdef STEVETEST
        enError errAddVehicleObjectives(const int& iVehicleID, const CPosition& posVehiclePosition, M_PTR_I_OBJECTIVE_PARAMETERS_BASE_t& ptr_miopObjectives,
                PTR_M_INT_PTR_M_INT_PATHINFORMATION_t& mipmipthDistanceBasedOnLineSegments, const bool& bPlanToClosestEdge = false);
        enError errAddVehicleObjectivesGround(const int& iVehicleID, const CPosition& posVehiclePosition, M_PTR_I_OBJECTIVE_PARAMETERS_BASE_t& ptr_miopObjectives,
                PTR_M_INT_PTR_M_INT_PATHINFORMATION_t& mipmipthDistanceBasedOnLineSegments);
#endif  //STEVETEST
#ifdef STEVETEST
        enError errFindShortestPath(const int& iStartID, const int& iEndID,
                M_INT_PTR_M_INT_PATHINFORMATION_t& mipmipthDistanceBasedOnLineSegments,
                D_POSITION_t& dposPathPositions,
                stringstream& sstrErrorMessage);
#endif  //STEVETEST

        
        enError errInitializeGraphBase();
        bool bBoundaryViolationExists(const V_WAYPOINT_t& vWaypoints, stringstream& sstrErrorMessage);

        enError errSmoothPath(D_POSITION_t& dposPath, const double& dTurnRadius_m,
                double& dHeadingInitial_rad, double& dHeadingFinal_rad, V_WAYPOINT_t& vwayWaypoints);

#ifdef STEVETEST
        enError errGenerateWaypoints(c_VehicleBase& cvbVehicle, c_ObjectiveParametersBase& cObjectiveParametersBase,
                PTR_M_INT_PTR_M_INT_PATHINFORMATION_t& mipmipthDistanceBasedOnLineSegments,
                CTrajectoryParameters::enPathType_t enpathType = CTrajectoryParameters::pathTurnStraightTurn,
                const bool bFirstObjective = false);
#endif  //#ifdef STEVETEST

        enError errGenerateWaypoints(const PlanningParameters& planningParameters,const CPathInformation& pthifPath,std::vector<CWaypoint>& waypoints);
    
        bool isGenerateWaypoints(const std::shared_ptr<n_FrameworkLib::CPathInformation>& pathInformation,
                                const double& startingHeading_deg, const double& endingHeading_deg,
                                const double& turnRadius_m, const CTrajectoryParameters::enPathType_t& enpathType,const double& minimumWaypointSeparation,
                                std::vector<afrl::cmasi::Waypoint*>& planWaypoints);

        enError errFindShortestPathLinear(std::shared_ptr<CPathInformation>& pathInformation);
        enError errFindShortestPathLinear(const CPosition& posPositionStart, const CPosition& posPositionEnd, PTR_DEQUE_POSITION_t& ptr_dqposShortestPath);
        enError errFindShortestPathLinear(const CPosition& posPositionStart, const int& iIdEnd, const CPosition& posPositionEnd,
                PTR_M_INT_PATHINFORMATION_t& ptr_mipthDistanceMapStart,
                PTR_M_INT_PATHINFORMATION_t& ptr_mipthDistanceMapEnd);

        enError errFindShortestPathGround(const CPosition& posPositionStart, const CPosition& posPositionEnd, PTR_DEQUE_POSITION_t& ptr_dqposShortestPath);
        enError errFindShortestPathGround(const CPosition& posPositionStart,
                const int& iIdEnd, const CPosition& posPositionEnd,
                PTR_M_INT_PATHINFORMATION_t& ptr_mipthDistanceMapStart,
                PTR_M_INT_PATHINFORMATION_t& ptr_mipthDistanceMapEnd);

        bool bFindIntersection(const V_POSITION_t&vposVerticiesBase, V_POLYGON_t& vPolygons, const CPosition& posPositionA, const CPosition& posPositionB,
                const int32_t& i32IndexA = -1, const int32_t& i32IndexB = -1);
    public: //inline methods/functions

        enError errGetDistance(const int& iFromID, const int& iToID, double& dDistance,
                PTR_M_INT_PTR_M_INT_PATHINFORMATION_t& ptr_mipmipthDistanceBasedOnLineSegments) {
            enError errReturn(errVerticiesNotFound);
            if ((ptr_mipmipthDistanceBasedOnLineSegments->find(iFromID) != ptr_mipmipthDistanceBasedOnLineSegments->end())&&
                    (ptr_mipmipthDistanceBasedOnLineSegments->operator[](iFromID)->find(iToID) != ptr_mipmipthDistanceBasedOnLineSegments->operator[](iFromID)->end())) {
                dDistance = ptr_mipmipthDistanceBasedOnLineSegments->operator[](iFromID)->operator[](iToID).iGetLength();
                errReturn = errNoError;
            }
            return (errReturn);
        };

        enError errAddPolygon(const int& iUniqueID, V_POSITION_IT_t itBegin, V_POSITION_IT_t itEnd, bool bKeepInZone = true, double dPolygonExpansionDistance = 0.0) {
            enError errReturn(errNoError);

            // if there is a polygon with this ID, then delete it and insert this one
            bool bExistingID(false);
            for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++) {
                if (itPolygon->iGetID() == iUniqueID) {
                    bExistingID = true;
                    itPolygon->ResetPolygon();
                    itPolygon->plytypGetPolygonType().bGetKeepIn() = bKeepInZone;
                    itPolygon->viGetVerticies().clear();
                    itPolygon->dGetPolygonExpansionDistance() = dPolygonExpansionDistance;
                    for (; itBegin != itEnd; itBegin++) {
                        vposGetVerticiesBase().push_back(*itBegin);
                        itPolygon->viGetVerticies().push_back(static_cast<int> (vposGetVerticiesBase().size()) - 1);
                    }
                    if (itPolygon->errFinalizePolygon(vposGetVerticiesBase()) != CPolygon::errNoError) {
                        errReturn = errPolygonCreation;
                    }
                    break;
                } //if(itPolygon->iGetID() == iUniqueID)
            }

            if (!bExistingID) {
                CPolygon cPolygon(iUniqueID);
                cPolygon.plytypGetPolygonType().bGetKeepIn() = bKeepInZone;
                cPolygon.dGetPolygonExpansionDistance() = dPolygonExpansionDistance;
                for (; itBegin != itEnd; itBegin++) {
                    vposGetVerticiesBase().push_back(*itBegin);
                    cPolygon.viGetVerticies().push_back(static_cast<int> (vposGetVerticiesBase().size()) - 1);
                }
                if (cPolygon.errFinalizePolygon(vposGetVerticiesBase()) == CPolygon::errNoError) {
                    vplygnGetPolygons().push_back(cPolygon);
                } else {
                    errReturn = errPolygonCreation;
                }
            } //if(!bExistingID)

            return (errReturn);
        };

        enError errExpandContractPolygons_m(const double& dDistance_m) {
            enError errReturn(errNoError);

            for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++) {
                if (itPolygon->plytypGetPolygonType().bGetExpandable()) {
                    itPolygon->dGetPolygonExpansionDistance() = dDistance_m;
                } else if (itPolygon->plytypGetPolygonType().bGetShrinkable()) {
                    itPolygon->dGetPolygonExpansionDistance() = -dDistance_m;
                }
            }

            return (errReturn);
        };

        enError errFinalizePolygons(void) {
            enError errReturn(errNoError);

            //merge must be after finalize, cause finalize expands polygons
            errReturn = errExpandAndMergePolygons();

            //run any functions that are needed to get the polygons ready for the visibility graph
            for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++) {
                itPolygon->errFinalizePolygon(vposGetVerticiesBase());
            }

            return (errReturn);
        };

        void StreamPolygons(ostream &os) {
            os << "{";
            for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++) {
                os << "[";
                itPolygon->StreamPolygonMatlab(os, vposGetVerticiesBase());
                os << "]" << std::endl;
                ;
            }
            os << "}";
        };

        void StreamPolygonsPython(ostream &os) {
            for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++) {
                //os << "[";
                itPolygon->StreamPolygonPython(os, vposGetVerticiesBase());
                //os << "]" << std::endl;;
            }
        };

        void StreamPolygonsCPP(ostream &os) {
            os << endl;
            for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++) {
                itPolygon->StreamPolygonCPP(os, vposGetVerticiesBase());
                os << std::endl;
                ;
            }
            os << endl;
        };

        //void StreamEdgesCurrent(ostream &os)
        //{
        //    os << "[";    
        //    for(CEdge::V_EDGE_CONST_IT_t itEdge=veGetEdgesVisibleCurrent().begin();itEdge!=veGetEdgesVisibleCurrent().end();itEdge++)
        //    {
        //        os << "[";
        //        os << vposGetVerticiesCurrent()[itEdge->first];
        //        os << ",";
        //        os << vposGetVerticiesCurrent()[itEdge->second];
        //        os << ",";
        //        os << itEdge->iGetLength();
        //        os << "]" << std::endl;;
        //    }
        //    os << "]";
        //};

        void SaveGraphVizFileShortestPaths(const int& iIndexVertex, const string& strPathOutput, const string& strFileName = string("VisibilityGraphShortestPath.dot")) {
            string strPathFileName = strPathOutput + "\\" + strFileName;
            std::ofstream dot_file(strPathFileName.c_str());

            dot_file << "digraph D {\n"
                    << "  rankdir=LR\n"
                    << "  size=\"7.5,9\"\n"
                    << "  ratio=\"fill\"\n"
                    //<< "  rotate=90\n"
                    << "  edge[style=\"bold\"]\n" << "  node[shape=\"circle\"]\n";

            boost::graph_traits < GRAPH_LIST_VEC_t >::vertex_iterator vi, vend;
#if !defined(WIN32)
            for (tie(vi, vend) = vertices(edglstvecGetGraph()); vi != vend; ++vi)
#else
            for (std::tie(vi, vend) = vertices(edglstvecGetGraph()); vi != vend; ++vi)
#endif
            {
                if (*vi == vvvtxGetVertexParentBase()[iIndexVertex][*vi]) {
                    continue;
                }
                dot_file << vvvtxGetVertexParentBase()[iIndexVertex][*vi] << " -> " << *vi << "[label=\"" << vviGetVertexDistancesBase()[iIndexVertex][*vi] << "\"";
                dot_file << ", color=\"black\"";
                dot_file << "]";
                dot_file << std::endl;
            }

            dot_file << "}";
        }

        void SaveGraphVizFileFull(const string& strPathOutput, const string& strFileName = string("VisibilityGraphFull.dot")) {
            string strPathFileName = strPathOutput + "\\" + strFileName;
            std::ofstream dot_file(strPathFileName.c_str());

            dot_file << "digraph D {\n"
                    << "  rankdir=LR\n"
                    << "  size=\"7.5,9\"\n"
                    << "  ratio=\"fill\"\n"
                    << "  rotate=90\n"
                    << "  edge[style=\"bold\"]\n" << "  node[shape=\"circle\"]\n";

            boost::property_map<GRAPH_LIST_VEC_t, boost::edge_weight_t>::type weightmap = get(boost::edge_weight, edglstvecGetGraph());
            boost::graph_traits < GRAPH_LIST_VEC_t >::edge_iterator ei, ei_end;
#ifndef _WIN32
            for (tie(ei, ei_end) = edges(edglstvecGetGraph()); ei != ei_end; ++ei)
#else
            for (std::tie(ei, ei_end) = edges(edglstvecGetGraph()); ei != ei_end; ++ei)
#endif
            {
                boost::graph_traits < GRAPH_LIST_VEC_t >::edge_descriptor e = *ei;
                boost::graph_traits < GRAPH_LIST_VEC_t >::vertex_descriptor
                u = source(e, edglstvecGetGraph()), v = target(e, edglstvecGetGraph());
                dot_file << u << " -> " << v << "[label=\"" << get(weightmap, e) << "\"";
                dot_file << ", color=\"grey\"";
                dot_file << "]";
                dot_file << std::endl;
            }
            dot_file << "}";
        }

        double dDistanceFromPointToSegment(const CPosition& posPoint, const CPosition& posEndA, const CPosition& posEndB, const double dLengthSegment_m) {
            double dDistanceToSegment(0.0);

            // from Derek's code
            //        point t
            //        segment a b 
            //    xyPoint p(t);
            //    xyPoint q = p - a;
            //    double ql = q.len();
            //    xyPoint r = b - a;
            //    double rl = r.len();
            //    if( ql < 1e-10 ) return ql;
            //    if( rl < 1e-10 ) return ql;
            //    return( (r.x*q.y - q.x*r.y)/(ql*rl) );
#ifndef STEVETEST
            double x1(posEndA.m_north_m);
            double y1(posEndA.m_east_m);
            double x2(posEndB.m_north_m);
            double y2(posEndB.m_east_m);
            double pointX(posPoint.m_north_m);
            double pointY(posPoint.m_east_m);


            //double FindDistanceToSegment(double x1, double y1, double x2, double y2, double pointX, double pointY)
            //{
            double diffX = x2 - x1;
            float diffY = y2 - y1;
            if ((diffX == 0) && (diffY == 0)) {
                diffX = pointX - x1;
                diffY = pointY - y1;
                return sqrt(diffX * diffX + diffY * diffY);
            }

            float t = ((pointX - x1) * diffX + (pointY - y1) * diffY) / (diffX * diffX + diffY * diffY);

            if (t < 0) {
                //point is nearest to the first point i.e x1 and y1
                diffX = pointX - x1;
                diffY = pointY - y1;
            } else if (t > 1) {
                //point is nearest to the end point i.e x2 and y2
                diffX = pointX - x2;
                diffY = pointY - y2;
            } else {
                //if perpendicular line intersect the line segment.
                diffX = pointX - (x1 + t * diffX);
                diffY = pointY - (y1 + t * diffY);
            }

            //returning shortest distance
            dDistanceToSegment = sqrt(diffX * diffX + diffY * diffY);

#else   //#ifdef STEVETEST


            if (dLengthSegment_m < 1.0e-10) {
                dDistanceToSegment = posEndA.relativeDistance2D_m(posPoint);
            } else {
                double dDistanceEndAToPoint = posEndA.relativeDistance2D_m(posPoint);
                if (dDistanceEndAToPoint < 1.0e-10) {
                    dDistanceToSegment = dDistanceEndAToPoint;
                } else {
#ifndef STEVETEST
                    double dDistanceEndBToPoint = posEndB.relativeDistance2D_m(posPoint);
                    //dDistanceToSegment = (dDistanceEndAToPoint + dDistanceEndBToPoint)/(dLengthSegment_m);
                    dDistanceToSegment = (dDistanceEndAToPoint + dDistanceEndBToPoint) / (2.0);
#else   //#ifdef STEVETEST
                    CPosition posQ(posPoint);
                    posQ -= posEndA;
                    CPosition posR(posEndB);
                    posR -= posEndA;

                    dDistanceToSegment = fabs(((posR.m_north_m * posQ.m_east_m) - (posQ.m_north_m * posR.m_east_m)) / (dDistanceEndAToPoint * dLengthSegment_m));
#endif  //STEVETEST
                }
            }
#endif  //STEVETEST

            return (dDistanceToSegment);
        }



        //%=============================================================================
        //% turndir
        //%   turn specifies the direction of the turn.  turn is positive for a ccw
        //%   turn and negative for a cw turn.  0 is returned if the next path requires
        //%   no turn.  Currently, we are on the path specified by q1.  The path we 
        //%   are switching to is q2.
        //%=============================================================================
        //% 
        //function turn = turndir(q1,q2)
        //
        //   %same as tmp = cross([q1 0],[q2 0]);
        //   %        turn = sign(tmp);
        //   turn = sign( q1(1)*q2(2) - q1(2)*q2(1) );
        //   
        //%end turndir

        CCircle::enTurnDirection_t turnDirection(const CPosition& posQ1, const CPosition& posQ2) {
            double dTemp = (posQ1.m_north_m * posQ2.m_east_m)-(posQ1.m_east_m * posQ2.m_north_m);
            int iReturn(static_cast<int> ((n_Const::c_Convert::bCompareDouble(dTemp, 0.0, n_Const::c_Convert::enEqual) ? (0.0) : (dTemp / fabs(dTemp)))));
            return (static_cast<CCircle::enTurnDirection_t> (iReturn));
        };
        //
        //%=============================================================================
        //% GetKappa
        //%   Returns the value of kappa that makes the length of the path segment and 
        //%   the length of the constrained turn equal to within 2^(-n) where n is a
        //%   positive integer.
        //%=============================================================================
        //%     
        //function a = GetKappa(r,beta,n)
        //    a = 0;
        //    b = 1;
        //    for i = 1:n
        //        L = Lambda(r,(a + b)/2,beta);
        //        if (L == 0)
        //            a = (a + b)/2;
        //            return
        //        elseif (L > 0)
        //            b = (a + b)/2;
        //        else
        //            a = (a + b)/2;
        //        end;
        //    end;
        //    
        //% end GetKappa

        double dGetKappa(const double& dR, const double& dBeta, const int& iN) {
            double dA(0.0);
            double dB(1.0);
            for (int iCount = 0; iCount < iN; iCount++) {
                double dL = dLambda(dR, (dA + dB) / 2.0, dBeta);
                if (dL <= 0.0) {
                    dA = (dA + dB) / 2.0;
                } else {
                    dB = (dA + dB) / 2.0;
                }
            }
            return (dA);
        };
        //
        //%=============================================================================
        //% Lambda
        //%   Returns the value of the distance between the path segment and the
        //%   constrained turn for the angle beta between the successive path segments,
        //%   the value k (i.e. kappa which lies between 0 and 1), and the turning 
        //%   radius r
        //%=============================================================================
        //%     
        //function L = Lambda(r,k,beta)
        //    sb = sin(beta/2);
        //    if sb == 0,
        //        L = sqrt(3) + 1;
        //    else    
        //        sp = 1 + sb;
        //        sm = 1 - sb;
        //L = r * ( sqrt(4 - (sp + k*sm)^2 ) + (1 + k*(1/sb - 1))*cos(beta/2) ...
        //        + (beta - pi)/2 - 2*acos((sp + k*sm)/2) );
        //    end;
        //    
        //% end Lambda

        double dLambda(const double& dR, const double& dK, const double& dBeta) {
            double dL(0.0);
            double dSb(sin(dBeta / 2.0));
            if (n_Const::c_Convert::bCompareDouble(dSb, 0.0, n_Const::c_Convert::enEqual)) {
                dL = sqrt(3.0) + 1.0;
            } else {
                double dSp = 1.0 + dSb;
                double dSm = 1.0 - dSb;
                dL = dR * (sqrt(4.0 - pow((dSp + dK * dSm), 2.0)) +
                        (1.0 + dK * (1.0 / dSb - 1.0)) * cos(dBeta / 2.0) +
                        (dBeta - n_Const::c_Convert::dPi()) / 2.0 - 2.0 * acos((dSp + dK * dSm) / 2.0));
            }
            return (dL);
        };
        //
        //%=============================================================================
        //% getturncenter
        //%   Returns the center of the cicle so the plane passes through a waypoint.
        //%   p is the waypoint to pass through, q1 is a unit vector in the direction
        //%   of the current path segment, q2 is a unit vector in the direction of
        //%   the next path segment, and radius is the radius of the turn.
        //%   Assume that q1 and q2 are not parallel.
        //%=============================================================================
        //% 
        //function c = getturncenter(p,q1,q2,radius,kappa,beta)
        //
        //    v = q2 - q1;
        //    if norm(v) ~= 0, 
        //        v = v./norm(v);    
        //    end
        //    
        //    sb = sin(beta/2);
        //    if sb == 0,
        //        c = p;
        //    else
        //        c = p + radius*( 1 + kappa*(1/sb - 1) ).*v; 
        //    end;
        //    
        //%end getturncenter

        void GetTurnCenter(const CPosition& posP, const CPosition& posQ1, const CPosition& posQ2,
                const double& dRadius, const double& dKappa, const double& dBeta,
                CPosition& posTurnCenter) {
            CPosition posV(posQ2);
            posV -= posQ1;
            double dNormV = posV.absoluteDistance2D_m();
            if (!n_Const::c_Convert::bCompareDouble(dNormV, 0.0, n_Const::c_Convert::enEqual)) {
                posV /= dNormV;
            }

            double dSb(sin(dBeta / 2.0));
            posTurnCenter = posP;
            if (!n_Const::c_Convert::bCompareDouble(dSb, 0.0, n_Const::c_Convert::enEqual)) {
                posTurnCenter += posV * (dRadius * (1.0 + dKappa * (1.0 / dSb - 1.0)));
            }
        };
        //
        //%=============================================================================
        //% getlinevals
        //%   returns the values of the line m,b in y = mx + b, and vert is set to 0
        //%   if the line is x = b, then vert is set to 1 and b is returned
        //%=============================================================================
        //% 
        //function [vert, m, b] = getlinevals(p1,p2)
        //  
        //    tol = 1e-6;
        //    %The tolerance condition is necessary to prevent truncation errors 
        //    %for nearly parallel lines
        //    if (p1(1) == p2(1)) | (abs(p1(1) - p2(1)) < tol)
        //        vert = 1;
        //        m = 0;
        //        b = p1(1);
        //    else
        //        vert = 0;
        //        m = (p1(2) - p2(2)) / (p1(1) - p2(1));
        //        b = -m*p1(1) + p1(2);
        //    end;
        //    
        //%end getlinevals

        void GetLineIntervals(const CPosition& posP1, const CPosition& posP2, int& iVert, double& dM, double& dB) {
            if (n_Const::c_Convert::bCompareDouble(posP1.m_north_m, posP2.m_north_m, n_Const::c_Convert::enEqual)) {
                iVert = 1;
                dM = 0.0;
                dB = posP1.m_north_m;
            } else {
                iVert = 0;
                dM = (posP1.m_east_m - posP2.m_east_m) / (posP1.m_north_m - posP2.m_north_m);
                dB = -dM * posP1.m_north_m + posP1.m_east_m;
            }
        };

        //
        //%=============================================================================
        //% twoturndist
        //%   returns the distance to the start of the first turn assuming that
        //%   the center waypoint is at (0,0) and the center turn circle is at c
        //%   with radius R (-R for turning clockwise) and the waypoint segment is
        //%   vertical
        //%=============================================================================
        //% 
        //function [d, ct] = twoturndist(R,c)
        //    % solve d^2 + d*(-2*cy) + ( (R-cx)^2 + cy^2 - 4*R^2 )
        //    b = -c(2);
        //    a = (R-c(1))^2 + c(2)^2 - 4*R^2;
        //    
        //    if b^2 - a < 0,
        //        error('no intersection in twoturndist');
        //        d = 0;
        //        ct = [0, 0];
        //        return;
        //    end;
        //    
        //    d = abs( b + sqrt(b^2 - a) );
        //    ct = [R, -d];
        //
        //%end twoturndist

        void TwoTurnDist(const double& dR, const CPosition& posC, double& dD, CPosition& posCt) {
            double dB(-posC.m_east_m);
            double dA(pow((dR - posC.m_north_m), 2.0) + pow(posC.m_east_m, 2.0) - 4.0 * pow(dR, 2.0));

            if ((pow(dB, 2.0) - dA) < 0.0) {
                dD = 0.0;
                posCt.m_north_m = 0.0;
                posCt.m_east_m = 0.0;
            } else {
                dD = fabs(dB + sqrt(pow(dB, 2.0) - dA));
                posCt.m_north_m = dR;
                posCt.m_east_m = -dD;
            }
        };
        //
        //%=============================================================================
        //% getUturnCenter
        //%   Returns the center of the cicle so that allows the plane must follow to
        //%   perform a U-turn and continue of the same path.  
        //%=============================================================================
        //% 
        //function c = getUturnCenter(p,q1,radius)
        //
        //        c = p + radius*((7*pi/6)-sqrt(3)).*q1; 
        //    
        //%end getturncenter

        void GetUTurnCenter(const CPosition& posP, const CPosition& posQ1, const double& dRadius, CPosition& posC) {
            posC = posQ1;
            posC *= dRadius * ((7.0 * n_Const::c_Convert::dPi() / 6.0) - sqrt(3.0));
            posC += posP;

        };

        double dClockwiseAngle(const COMPLEX_D_t& cxdPoint1, const COMPLEX_D_t& cxdPoint2, const COMPLEX_D_t& cxdPoint3) {
            return std::arg((cxdPoint1 - cxdPoint2) / (cxdPoint3 - cxdPoint2));
        }


    public: //accessors

        V_POSITION_t& vposGetVerticiesBase() {
            return (m_vposVerticiesBase);
        };

        const V_POSITION_t& vposGetVerticiesBase()const {
            return (m_vposVerticiesBase);
        };

        V_POLYGON_t& vplygnGetPolygons() {
            return (m_vplygnPolygons);
        };

        const V_POLYGON_t& vplygnGetPolygons()const {
            return (m_vplygnPolygons);
        };

        V_EDGE_t& veGetEdgesVisibleBase() {
            return (m_veEdgesVisibleBase);
        };

        const V_EDGE_t& veGetEdgesVisibleBase()const {
            return (m_veEdgesVisibleBase);
        };

        std::vector<std::vector<int32_t>>& vviGetVertexDistancesBase() {
            return (m_vviVertexDistancesBase);
        };

        const std::vector<std::vector<int32_t>>& vviGetVertexDistancesBase()const {
            return (m_vviVertexDistancesBase);
        };

        V_V_VERTEX_DESCRIPTOR_t& vvvtxGetVertexParentBase() {
            return (m_vvvtxVertexParentBase);
        };

        const V_V_VERTEX_DESCRIPTOR_t& vvvtxGetVertexParentBase()const {
            return (m_vvvtxVertexParentBase);
        };

        GRAPH_LIST_VEC_t& edglstvecGetGraph() {
            return (*m_pedglstvecGraph);
        };

        const GRAPH_LIST_VEC_t& edglstvecGetGraph()const {
            return (*m_pedglstvecGraph);
        };

        GRAPH_LIST_VEC_t*& pedglstvecGetGraph() {
            return (m_pedglstvecGraph);
        };

        CPathInformation::enPathType& ptypeGetType() {
            return (m_ptypeType);
        };

        const CPathInformation::enPathType& ptypeGetType()const {
            return (m_ptypeType);
        };

        int& iGetLengthSegmentMinimum() {
            return (m_iLengthSegmentMinimum);
        };

        const int& iGetLengthSegmentMinimum()const {
            return (m_iLengthSegmentMinimum);
        };

    protected: //storage

        //initial polygons
        V_POSITION_t m_vposVerticiesBase;
        V_POLYGON_t m_vplygnPolygons;

        //visibility graph storage
        V_EDGE_t m_veEdgesVisibleBase;
        std::vector<std::vector<int32_t>> m_vviVertexDistancesBase; //m_viVertexDistances[u][v] => shortest distance from u to v
        V_V_VERTEX_DESCRIPTOR_t m_vvvtxVertexParentBase; //m_viVertexParent[u][v] => index of the parent vertex of v on route to the shortest path ro u
        GRAPH_LIST_VEC_t* m_pedglstvecGraph;

        // storage for generating waypoint paths
        CPathInformation::enPathType m_ptypeType;
        int m_iLengthSegmentMinimum;
    };

    ostream &operator<<(ostream &os, const CVisibilityGraph& visgRhs);

}; //namespace n_FrameworkLib
