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
// VisibilityGraph.cpp: implementation for the CVisibilityGraph class.
//
//    1. Add polygons    => enError errAddPolygon(const int& iUniqueID,V_POSITION_IT_t itBegin,V_POSITION_IT_t itEnd)
//    2. Finalize polygons => enError errFinalizePolygons(void)
//    3. Build visibility graph => enError errBuildVisibilityGraph(void)
//    4. Add extra vertices, e.g. vehicles/objectives => vposidVerticiesCurrent.push_back(CPosition())
//    5. Buld current visibility graph, i.e. find visible edges for each of the new vertices =>  enError errBuildVisibilityGraphCurrent(void)
//
//////////////////////////////////////////////////////////////////////


//#include "GlobalDefines.h"
#include "VisibilityGraph.h"
#include "Trajectory.h"
//#include "rasCObjective_RecoveryPoint.h"
//#include "Objective.h"
#include "visilibity.h"
#include "Waypoint.h"
#include "PlanningParameters.h"     //polygon expansion

#include <pugixml.hpp>


namespace n_FrameworkLib
{

//#define DEBUG_PRINTOUTS
#ifdef DEBUG_PRINTOUTS
#define PRINT_DEBUG(MESSAGE) std::cerr << "VG-VG-VG-VG CVisibilityGraph:: " << __LINE__  << MESSAGE << std::endl;std::cerr.flush();
#else
#define PRINT_DEBUG(MESSAGE)
#endif

#define CCA_CERR_FILE_LINE(MESSAGE) std::cerr << "VG-VG-VG-VG CVisibilityGraph:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cerr.flush();
#define CCA_COUT_FILE_LINE(MESSAGE) std::cout << "VG-VG-VG-VG CVisibilityGraph:: " << __FILE__ << ":" << __LINE__ << ":" << MESSAGE << std::endl;std::cout.flush();

    
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::CVisibilityGraph()
    : m_pedglstvecGraph(0),
    m_ptypeType(CPathInformation::ptypeEqualLength),
    m_iLengthSegmentMinimum(1)
    {
    }
    
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::~CVisibilityGraph(void)
    {
        if (pedglstvecGetGraph())
        {
            delete pedglstvecGetGraph();
        }
        pedglstvecGetGraph() = 0;
    }
    
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::enError CVisibilityGraph::errExpandAndMergePolygons()
    {
        enError errReturn(errNoError);
        
        if(!vplygnGetPolygons().empty())
        {
        
        unsigned int k;

        std::vector< VisiLibity::Polygon > expandList;
        std::vector< double > expandValues;
        std::vector< VisiLibity::Polygon > shrinkList;
        std::vector< double > shrinkValues;

        // translate to VisiLibity data structure
        for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++)
        {
            std::vector< VisiLibity::Point > polygonVertices;
            for (auto itVertex = itPolygon->m_viVerticies.begin(); itVertex != itPolygon->m_viVerticies.end(); itVertex++)
                polygonVertices.push_back(VisiLibity::Point(vposGetVerticiesBase()[*itVertex].m_east_m, vposGetVerticiesBase()[*itVertex].m_north_m));
            VisiLibity::Polygon poly(polygonVertices);

            // remove excess points
            poly.eliminate_redundant_vertices(1.0);

            double epsilon(1e-8);
            // ensure that the polygon is simple
            if (!poly.is_simple(epsilon))
                return (errPolygonCreation);

            // ensure that the polygon is properly oriented
            if (poly.area() < 0)
                poly.reverse();

            if (itPolygon->plytypGetPolygonType().bGetKeepIn())
            {
                shrinkList.push_back(poly);
                double dPolygonExpansionDistance(0.0); //no expansion or shrinking
                shrinkValues.push_back(dPolygonExpansionDistance);
            }
            else
            {
                // keep out boundary
                expandList.push_back(poly);
                double dPolygonExpansionDistance(0.0);
                dPolygonExpansionDistance = (itPolygon->dGetPolygonExpansionDistance() < 0.0) ? (0.0) : (itPolygon->dGetPolygonExpansionDistance()); // don't let it shrink!
                expandValues.push_back(dPolygonExpansionDistance);
            }
        }

        // expand polygons
        std::vector< VisiLibity::Polygon > expandedPolygons;
        if (!VisiLibity::Polygon::offset_polygons(expandList, expandedPolygons, expandValues, 1e-8))
            return (errPolygonMerging);
        for (k = 0; k < expandedPolygons.size(); k++)
            expandedPolygons[k].eliminate_redundant_vertices(1.0);

        // shrink polygons
        std::vector< VisiLibity::Polygon > shrunkenPolygons;
        if (!VisiLibity::Polygon::offset_polygons(shrinkList, shrunkenPolygons, shrinkValues, 1e-8))
            return (errPolygonMerging);
        for (k = 0; k < shrunkenPolygons.size(); k++)
            shrunkenPolygons[k].eliminate_redundant_vertices(1.0);

        // clear out all the polygons that existed before the merge
        vposGetVerticiesBase().clear();
        vplygnGetPolygons().clear();

        // translate back from VisiLibity data structure
        for (k = 0; k < shrunkenPolygons.size(); k++)
        {
            if (fabs(shrunkenPolygons[k].area()) > 1.0)
            {
                CPolygon cPolygon(vplygnGetPolygons().size() + 1);
                cPolygon.plytypGetPolygonType().bGetKeepIn() = true;
                for (unsigned int n = 0; n < shrunkenPolygons[k].n(); n++)
                {
                    cPolygon.viGetVerticies().push_back(vposGetVerticiesBase().size());
                    vposGetVerticiesBase().push_back(CPosition(shrunkenPolygons[k][n].y(), shrunkenPolygons[k][n].x()));
                }
                vplygnGetPolygons().push_back(cPolygon);
            }
        }

        for (k = 0; k < expandedPolygons.size(); k++)
        {
            if (fabs(expandedPolygons[k].area()) > 1.0)
            {
                CPolygon cPolygon(vplygnGetPolygons().size() + 1);
                cPolygon.plytypGetPolygonType().bGetKeepIn() = false;
                for (unsigned int n = 0; n < expandedPolygons[k].n(); n++)
                {
                    cPolygon.viGetVerticies().push_back(vposGetVerticiesBase().size());
                    vposGetVerticiesBase().push_back(CPosition(expandedPolygons[k][n].y(), expandedPolygons[k][n].x()));
                }
                vplygnGetPolygons().push_back(cPolygon);
            }
        }

        }       //if(!vplygnGetPolygons().empty())
        return (errReturn);
    }
    
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::enError CVisibilityGraph::errBuildVisibilityGraph(void)
    {
        PRINT_DEBUG("*DEBUG*")
        //TODO:: what to do aboout errors?????

        enError errReturn(errNoError);

        //TODO::
        //    1) build a graph of existing edges (edges of polygons)
        //    2) check line segments connecting each vertex with all other vertices to see if there is an intersection of the existing edges
        //        - only need to check one direction, i.e. don't need to check both (A,B) and (B,A)
        //        - for convex polygons, do not need to check line segments connecting vertices on the polygon
        //        - for concave polygons, need to check line segments connecting the polygon vertices and, for visible segments, need to check inside/outside of the polygon
        //        - use the locations of the polygons to check closer edges first
        //        - add any new edges found to an edge container


        //TODO::
        // find any keep-in zones.
        // if keep-out edges go out of the keep-in zone then don't add it a valid


        //clear out any old edges
        veGetEdgesVisibleBase().clear();
        //add all of the visible edges that we already know about
        stringstream sstrErrorMessage;
        for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++)
        {
            if (itPolygon->plytypGetPolygonType().bGetKeepIn())
            {
                // add all of the keep-in zone edges
                for (V_EDGE_IT_t itEdge = itPolygon->veGetPolygonEdges().begin(); itEdge != itPolygon->veGetPolygonEdges().end(); itEdge++)
                {
                    veGetEdgesVisibleBase().push_back(*itEdge);
                }
            }
            else //if(itPolygon->plytypGetPolygonType().bGetKeepInZone())
            {
                for (V_EDGE_IT_t itEdge = itPolygon->veGetPolygonEdges().begin(); itEdge != itPolygon->veGetPolygonEdges().end(); itEdge++)
                {
                    bool bGoodEdge(true);
                    double dX0 = vposGetVerticiesBase()[itEdge->first].m_north_m;
                    double dY0 = vposGetVerticiesBase()[itEdge->first].m_east_m;
                    double dZ0 = vposGetVerticiesBase()[itEdge->first].m_altitude_m;
                    double dX1 = vposGetVerticiesBase()[itEdge->second].m_north_m;
                    double dY1 = vposGetVerticiesBase()[itEdge->second].m_east_m;
                    double dZ1 = vposGetVerticiesBase()[itEdge->second].m_altitude_m;
                    double dMid_X = (dX1 - dX0) / 2.0 + dX0;
                    double dMid_Y = (dY1 - dY0) / 2.0 + dY0;
                    double dMid_Z = (dZ1 - dZ0) / 2.0 + dZ0;
                    for (V_POLYGON_IT_t itPolygonCheck = vplygnGetPolygons().begin(); itPolygonCheck != vplygnGetPolygons().end(); itPolygonCheck++)
                    {
                        if (itPolygonCheck->plytypGetPolygonType().bGetKeepIn())
                        {
                            // check to make sure that the current edge does not overlap a keep-in boundary
                            // check start, end, and middle points to see if they are all in or out of the boundary
                            bool bOneIn = itPolygonCheck->InPolygon(dX0, dY0, dZ0, vposGetVerticiesBase(), sstrErrorMessage);
                            bool bTwoIn = itPolygonCheck->InPolygon(dX1, dY1, dZ1, vposGetVerticiesBase(), sstrErrorMessage);
                            bool bThreeIn = itPolygonCheck->InPolygon(dMid_X, dMid_Y, dMid_Z, vposGetVerticiesBase(), sstrErrorMessage);
                            if ((bOneIn != bTwoIn) || (bOneIn != bThreeIn))
                            {
                                bGoodEdge = false;
                                break;
                            }
                        }
                    }
                    if (bGoodEdge)
                    {
                        veGetEdgesVisibleBase().push_back(*itEdge);
                    }
                }
            } //if(itPolygon->plytypGetPolygonType().bGetKeepInZone())
        } //for(V_POLYGON_IT_t itPolygon=vplygnGetPolygons().begin();itPolygon!=vplygnGetPolygons().end();itPolygon++)

#ifdef STEVETEST
        // find all the visible edges on non-convex polygons (these may cross other polygons, so need to check them for intersections)
        for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++)
        {
            itPolygon->errFindSelfVisibleEdges(vposGetVerticiesBase());
        }
#endif    //STEVETEST


        // build a map of distance to the other polygons (store in polygons)
        for (V_POLYGON_IT_t itPolygon = vplygnGetPolygons().begin(); itPolygon != vplygnGetPolygons().end(); itPolygon++)
        {
            V_POLYGON_IT_t itPolygonBegin = vplygnGetPolygons().begin();
            V_POLYGON_IT_t itPolygonEnd = vplygnGetPolygons().end();
            itPolygon->errCalculateDistanceToOtherPolygons(itPolygonBegin, itPolygonEnd);
        }

        //based on order of polygons:
        //    create line segments using vertices from current polygon to every other polygon
        //    for each line segment check all polygon edges for intersections
        if (!vplygnGetPolygons().empty())
        {
            for (V_POLYGON_IT_t itPolygons1 = vplygnGetPolygons().begin(); itPolygons1 != (vplygnGetPolygons().end() - 1); itPolygons1++)
            {
                for (V_POLYGON_IT_t itPolygons2 = (itPolygons1 + 1); itPolygons2 != vplygnGetPolygons().end(); itPolygons2++)
                {
                    itPolygons1->errFindVisibleEdges(vposGetVerticiesBase(), itPolygons2, veGetEdgesVisibleBase());
                }
            }
        }

        //based on order of polygons:
        //    check each of the extra edges, generated earlier to make sure they don't intersect other polygons
        if (vplygnGetPolygons().size() > 1)
        {
            V_POLYGON_IT_t itPolygons1 = vplygnGetPolygons().begin();
            for (; itPolygons1 != (vplygnGetPolygons().end() - 1); itPolygons1++)
            {
                for (V_POLYGON_IT_t itPolygons2 = (itPolygons1 + 1); itPolygons2 != vplygnGetPolygons().end(); itPolygons2++)
                {
                    if (itPolygons2 != itPolygons1)
                    {
                        itPolygons1->errAddExtraVisibleEdges(vposGetVerticiesBase(), itPolygons2, veGetEdgesVisibleBase());
                    }
                }
            }
            //need to check the last polygon
            itPolygons1 = vplygnGetPolygons().end() - 1;
            for (V_POLYGON_IT_t itPolygons2 = vplygnGetPolygons().begin(); itPolygons2 != (vplygnGetPolygons().end() - 1); itPolygons2++)
            {
                itPolygons1->errAddExtraVisibleEdges(vposGetVerticiesBase(), itPolygons2, veGetEdgesVisibleBase());
            }
        }
        else if (!vplygnGetPolygons().empty()) //if(vplygnGetPolygons().size() > 1)
        {
            vplygnGetPolygons().begin()->errAddExtraVisibleEdges(vposGetVerticiesBase(), vplygnGetPolygons().begin(), veGetEdgesVisibleBase());
        }
        PRINT_DEBUG("*DEBUG*")
        return (errReturn);
    }
    
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::enError CVisibilityGraph::errBuildVisibilityGraph(PTR_GRAPH_REGION_t& ptr_GraphRegion)
    {
        enError errReturn(errNoError);
        PRINT_DEBUG("*DEBUG*")

        uxas::common::utilities::CUnitConversions cUnitConversions;

        std::map<uint32_t, int> muiiIdToIndex;
        //use predefined graph region as the base graph

        //1) add the nodes (vposGetVerticiesBase()) and create IDs (veGetEdgesVisibleBase())
        vposGetVerticiesBase().clear();
        for (auto itNode = ptr_GraphRegion->getNodeList().begin(); itNode != ptr_GraphRegion->getNodeList().end(); itNode++)
        {
            double dNorth_m(0.0);
            double dEast_m(0.0);
            cUnitConversions.ConvertLatLong_degToNorthEast_m((*itNode)->getCoordinates()->getLatitude(), (*itNode)->getCoordinates()->getLongitude(), dNorth_m, dEast_m);

            int iVertexID = static_cast<int> (vposGetVerticiesBase().size());
            vposGetVerticiesBase().push_back(CPosition(dNorth_m, dEast_m, (*itNode)->getCoordinates()->getAltitude()));

            //veGetEdgesVisibleBase().push_back(static_cast<int>(iVertexID));
            muiiIdToIndex[(*itNode)->getNodeID()] = iVertexID;
            //PRINT_DEBUG("iVertexID[" << iVertexID << "] NodeID[" << (*itNode)->getNodeID() << "] dNorth_m[" << dNorth_m << "] dEast_m[" << dEast_m << "]")
        } //for(auto itNode=ptr_GraphRegion->getNodeList().begin();itNode!=ptr_GraphRegion->getNodeList().end();itNode++)

        //2) build edge list (veGetPolygonEdges())

        veGetEdgesVisibleBase().clear();
        for (auto itEdge = ptr_GraphRegion->getEdgeList().begin(); itEdge != ptr_GraphRegion->getEdgeList().end(); itEdge++)
        {
            if ((muiiIdToIndex.find((*itEdge)->getStartNode()) != muiiIdToIndex.end()) && (muiiIdToIndex.find((*itEdge)->getEndNode()) != muiiIdToIndex.end()))
            {
                int iVertexStartID(muiiIdToIndex[(*itEdge)->getStartNode()]);
                int iVertexEndID(muiiIdToIndex[(*itEdge)->getEndNode()]);
                for (auto itWaypoint = (*itEdge)->getWaypoints().begin(); itWaypoint != (*itEdge)->getWaypoints().end(); itWaypoint++)
                {
                    double dNorth_m(0.0);
                    double dEast_m(0.0);
                    cUnitConversions.ConvertLatLong_degToNorthEast_m((*itWaypoint)->getLatitude(), (*itWaypoint)->getLongitude(), dNorth_m, dEast_m);
                    int iVertexID = static_cast<int> (vposGetVerticiesBase().size());
                    vposGetVerticiesBase().push_back(CPosition(dNorth_m, dEast_m, (*itWaypoint)->getAltitude()));

                    int iDistance = static_cast<int> (vposGetVerticiesBase()[iVertexStartID].relativeDistance2D_m(vposGetVerticiesBase()[iVertexID]));
                    CEdge eEdge(iVertexStartID, iVertexID, iDistance);
                    veGetEdgesVisibleBase().push_back(eEdge);
                    iVertexStartID = iVertexID;
                }

                int iDistance = static_cast<int> (vposGetVerticiesBase()[iVertexStartID].relativeDistance2D_m(vposGetVerticiesBase()[iVertexEndID]));
                CEdge eEdge(iVertexStartID, iVertexEndID, iDistance);
                veGetEdgesVisibleBase().push_back(eEdge);
            }
        }
        PRINT_DEBUG("*DEBUG*")
        return (errReturn);
    }
   
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    
    CVisibilityGraph::enError CVisibilityGraph::errBuildVisibilityGraphWithOsm(const string& osmFile)
    {
        enError errReturn(errNoError);

        uxas::common::utilities::CUnitConversions cUnitConversions;
        vposGetVerticiesBase().clear();

        pugi::xml_document xmldocConfiguration;
        std::ifstream ifsOperatorXML(osmFile);
        pugi::xml_parse_result result = xmldocConfiguration.load(ifsOperatorXML);

        std::unordered_map<uint64_t, int32_t> nodeIdVsIndex;
        std::unordered_multimap<int64_t,int64_t> wayIdVsNodeIds;
        
        if (result)
        {
            uint32_t countEdges(0);
            pugi::xml_node osmMap = xmldocConfiguration.child("osm");
            if (osmMap)
            {
                // first get a list of the roads (way's)
                for (pugi::xml_node ndCurrent = osmMap.child("way"); ndCurrent; ndCurrent = ndCurrent.next_sibling("way"))
                {
                    if (!ndCurrent.attribute("id").empty())
                    {
                        int64_t wayId = ndCurrent.attribute("id").as_int64();
                        bool isHighway(false);
                        std::vector<int64_t> nodes;
                        for (pugi::xml_node wayNode = ndCurrent.first_child(); wayNode; wayNode = wayNode.next_sibling())
                        {
                            if(strcmp(wayNode.name(),"nd") == 0)
                            {
                                if (!wayNode.attribute("ref").empty())
                                {
                                    nodes.push_back(wayNode.attribute("ref").as_int64());
                                }
                            }
                            // only save nodes and edges associated with highway's (i.e any road)
                            else if((!isHighway) && (strcmp(wayNode.name(),"tag") == 0))
                            {
                                if (!wayNode.attribute("k").empty())
                                {
                                    if(strcmp(wayNode.attribute("k").as_string(), "highway") == 0)
                                    {
                                        isHighway = true;
                                    }
                                }
                            }
                        }
                        if(isHighway)
                        {
                            countEdges++;
                            for(auto itNode=nodes.begin();itNode!=nodes.end();itNode++)
                            {
                                nodeIdVsIndex[*itNode] = 0;
                                wayIdVsNodeIds.insert(std::pair<int64_t,int64_t>(wayId,*itNode));
                            }
                        }
                    }
                    else        //if (!ndCurrent.attribute("id").empty())
                    {
                        CCA_CERR_FILE_LINE("OSM FILE:: parse XML string failed for osmFile[" << osmFile << "] :: could not find a 'way id'")
                    }
                }
                // next load the nodes associated with ways
                for (pugi::xml_node ndCurrent = osmMap.child("node"); ndCurrent; ndCurrent = ndCurrent.next_sibling("node"))
                {
                    //<node id="196779277" visible="true" version="2" changeset="2671787" timestamp="2009-09-29T01:02:14Z" user="woodpeck_fixbot" uid="147510" lat="39.9389700" lon="-83.8455730"/>
                    int64_t nodeId = 0;
                    if (!ndCurrent.attribute("id").empty())
                    {
                        nodeId = ndCurrent.attribute("id").as_int64();
                        // only load nodes associated with way's that are highway's
                        auto itIdToIndex = nodeIdVsIndex.find(nodeId);
                        if(itIdToIndex != nodeIdVsIndex.end())
                        {
                            if (!ndCurrent.attribute("lat").empty())
                            {
                                double lat = ndCurrent.attribute("lat").as_double();
                                if (!ndCurrent.attribute("lon").empty())
                                {
                                        double lon = ndCurrent.attribute("lon").as_double();
                                        double dNorth_m(0.0);
                                        double dEast_m(0.0);
                                        cUnitConversions.ConvertLatLong_degToNorthEast_m(lat,lon, dNorth_m, dEast_m);
                                        vposGetVerticiesBase().push_back(CPosition(dNorth_m, dEast_m,0.0));

                                        int iVertexID = static_cast<int> (vposGetVerticiesBase().size());
                                        itIdToIndex->second = iVertexID;
                                }
                                else        //if (!ndCurrent.attribute("lon").empty())
                                {
                                    CCA_CERR_FILE_LINE("OSM FILE:: parse XML string failed, could not find longitude for node id[" << nodeId << "]")
                                }       //if (!ndCurrent.attribute("lon").empty())
                            }       //if (!ndCurrent.attribute("lat").empty())
                            else
                            {
                                CCA_CERR_FILE_LINE("OSM FILE:: parse XML string failed, could not find longitude for node id[" << nodeId << "]")
                            }       //if (!ndCurrent.attribute("lat").empty())
                        }
                    }
                    else        //if (!ndCurrent.attribute("id").empty())
                    {
                        CCA_CERR_FILE_LINE("OSM FILE:: parse XML string failed, could not find node id[" << nodeId << "] ")
                    }       //if (!ndCurrent.attribute("id").empty())
                }       //ffor (pugi::xml_node ndCurrent = osmMap.child("node"); ndCurrent; ndCurrent = ndCurr ... 
                
                CCA_COUT_FILE_LINE("OSM FILE:: loaded [" << countEdges << "] ways and [" << vposGetVerticiesBase().size() << "] nodes.")
            }
            else        //if (osmMap)
            {
                CCA_CERR_FILE_LINE("OSM FILE:: parse XML string failed, could not find 'osm' section in osmFile[" << osmFile << "] ")
            }       //if (osmMap)
        } //if (result)
        else        //if (osmMap)
        {
            CCA_CERR_FILE_LINE("OSM FILE:: parse XML string failed for osmFile[" << osmFile << "]")
        }

        //3) build edge list (veGetPolygonEdges())

        veGetEdgesVisibleBase().clear();
        int64_t currentWayId(-1);
        std::unordered_map<uint64_t, int32_t>::iterator itStart(nodeIdVsIndex.end());
        
        for (auto itWayNodeIds = wayIdVsNodeIds.begin(); itWayNodeIds != wayIdVsNodeIds.end(); itWayNodeIds++)
        {
            if(itWayNodeIds->first != currentWayId)
            {
                itStart = nodeIdVsIndex.find(itWayNodeIds->second);
                if(itStart != nodeIdVsIndex.end())
                {
                    currentWayId = itWayNodeIds->first;
                }
                else
                {
                    currentWayId = -1;  //need to find a valid start point before proceeding
                    CCA_CERR_FILE_LINE("OSM FILE:: while building edges:: could not find index for node[" << itWayNodeIds->second << "]")
                }
            }
            else        //if(itWayNodeIds->first != currentWayId)
            {
                auto itEnd = nodeIdVsIndex.find(itWayNodeIds->second);
                if (itEnd != nodeIdVsIndex.end())
                {
                    int iVertexStartID(itStart->second);
                    int iVertexEndID(itEnd->second);

                    int iDistance = static_cast<int> (vposGetVerticiesBase()[iVertexStartID].relativeDistance2D_m(vposGetVerticiesBase()[iVertexEndID]));
                    CEdge eEdge(iVertexStartID, iVertexEndID, iDistance);
                    veGetEdgesVisibleBase().push_back(eEdge);
                    
                    itStart = itEnd;
                }
            }       //if(itWayNodeIds->first != currentWayId)
        }

        return (errReturn);
    }
    
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    
    CVisibilityGraph::enError CVisibilityGraph::errInitializeGraphBase()
    {
        enError errReturn(errNoError);
        PRINT_DEBUG("*DEBUG*")

        //TODO:: is there a better way to do this?
        std::vector<int32_t> viEdgeLengths;
        for (CEdge::V_EDGE_CONST_IT_t itEdge = veGetEdgesVisibleBase().begin(); itEdge != veGetEdgesVisibleBase().end(); itEdge++)
        {
            viEdgeLengths.push_back(itEdge->iGetLength());
        }

        PRINT_DEBUG("*DEBUG*")
        pedglstvecGetGraph() = new GRAPH_LIST_VEC_t(veGetEdgesVisibleBase().begin(),
                veGetEdgesVisibleBase().end(),
                viEdgeLengths.begin(),
                vposGetVerticiesBase().size());

        PRINT_DEBUG("*DEBUG* num_vertices(edglstvecGetGraph())[" << num_vertices(edglstvecGetGraph()) << "]")

        //reintialize the vertex parents
        vvvtxGetVertexParentBase().clear();
        V_VERTEX_DESCRIPTOR_t vvtxTemp(num_vertices(edglstvecGetGraph()));
        vvvtxGetVertexParentBase().resize(num_vertices(edglstvecGetGraph()), vvtxTemp);

        PRINT_DEBUG("*DEBUG* num_vertices(edglstvecGetGraph())[" << num_vertices(edglstvecGetGraph()) << "]")
        //reintialize the distance matrix
        vviGetVertexDistancesBase().clear();
        std::vector<int32_t> viTemp(num_vertices(edglstvecGetGraph()), 0);
        vviGetVertexDistancesBase().resize(num_vertices(edglstvecGetGraph()), viTemp);

        PRINT_DEBUG("*DEBUG* num_vertices(edglstvecGetGraph())[" << num_vertices(edglstvecGetGraph()) << "]")
        for (size_t szCountVerticies = 0; szCountVerticies < num_vertices(edglstvecGetGraph()); szCountVerticies++)
        {
            V_VERTEX_DESCRIPTOR_t vtxParents(num_vertices(edglstvecGetGraph()));
            std::vector<int32_t> viDistances(num_vertices(edglstvecGetGraph()));

            vertex_descriptor vtxCurrent = vertex(szCountVerticies, edglstvecGetGraph());
            boost::dijkstra_shortest_paths(edglstvecGetGraph(), vtxCurrent, boost::predecessor_map(&vtxParents[0]).distance_map(&viDistances[0]));

            vvvtxGetVertexParentBase()[szCountVerticies] = vtxParents;

            //TODO:: need to calculate the a vector of the distance matrix using distances and parents
            for (size_t szCountVerticies2 = 0; szCountVerticies2 < num_vertices(edglstvecGetGraph()); szCountVerticies2++)
            {
                vviGetVertexDistancesBase()[szCountVerticies][szCountVerticies2] = viDistances[szCountVerticies2];
            } //for(int szCountVerticies2=0;szCountVerticies2<num_vertices(edglstvecGetGraph());szCountVerticies2++)
        } //for(int szCountVerticies=0;szCountVerticies<num_vertices(edglstvecGetGraph());szCountVerticies++)
        PRINT_DEBUG("*DEBUG*")
        return (errReturn);
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    bool CVisibilityGraph::bFindIntersection(const V_POSITION_t&vposVerticiesBase, V_POLYGON_t& vPolygons, const CPosition& posPositionA, const CPosition& posPositionB,
            const int32_t& i32IndexA, const int32_t& i32IndexB)
    {
        bool bIntersects(false);
        for (auto itPolygons = vPolygons.begin(); itPolygons != vPolygons.end(); itPolygons++)
        {
            for (auto itEdge = itPolygons->veGetPolygonEdges().begin(); itEdge != itPolygons->veGetPolygonEdges().end(); itEdge++)
            {
                if (itEdge->bIntersection(vposVerticiesBase, posPositionA, posPositionB, i32IndexA, i32IndexB))
                {
                    bIntersects = true;
                    break;
                }
            }
        }
        return (bIntersects);
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////

    bool CVisibilityGraph::bBoundaryViolationExists(const V_WAYPOINT_t& vWaypoints, stringstream& sstrErrorMessage)
    {
        bool bReturn(false);

        // SIMPLE:: check to see if any of the waypoints are inside any keep in zones
        // TODO:: this does not check for violations by the path between waypoints!
        for (V_WAYPOINT_CONST_IT_t itWaypoint = vWaypoints.begin(); itWaypoint != vWaypoints.end(); itWaypoint++)
        {
            for (V_POLYGON_IT_t itPolygons = vplygnGetPolygons().begin(); itPolygons != (vplygnGetPolygons().end()); itPolygons++)
            {
                if (!itPolygons->plytypGetPolygonType().bGetKeepIn()) // only checking keep-out zones
                {
                    bReturn = itPolygons->InPolygon(itWaypoint->m_north_m, itWaypoint->m_east_m, itWaypoint->m_altitude_m, vposGetVerticiesBase(), sstrErrorMessage);
                    if (bReturn)
                    {
                        double dLatitude_deg(0.0);
                        double dLongitude_deg(0.0);
                        uxas::common::utilities::CUnitConversions cUnitConversions;
                        cUnitConversions.ConvertNorthEast_mToLatLong_deg(itWaypoint->m_north_m, itWaypoint->m_east_m, dLatitude_deg, dLongitude_deg);
                        sstrErrorMessage << "Violation of Polygon ID[" << itPolygons->iGetID() << "] at [" << dLatitude_deg << "," << dLongitude_deg << "] ([lat/long])" << endl;
                        break;
                    }
                }
            } //for(V_POLYGON_IT_t itPolygons=vplygnGetPolygons().begin();itPolygons!=(vplygnGetPolygons().end());itPolygons++)
            if (bReturn)
            {
                break;
            }
        } //for(V_WAYPOINT_CONST_IT_t itWaypoint=vWaypoints.begin();itWaypoint!=vWaypoints.end();itWaypoint++)

        return (bReturn);
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::enError CVisibilityGraph::errFindShortestPathLinear(std::shared_ptr<CPathInformation>& pathInformation)
    {
        enError errReturn(errNoError);
        int32_t i32IdEnd(1000); // dummy Id
        PTR_M_INT_PATHINFORMATION_t ptr_mipthDistanceMapStart(new M_INT_PATHINFORMATION_t);
        PTR_M_INT_PATHINFORMATION_t ptr_mipthDistanceMapEnd(new M_INT_PATHINFORMATION_t);

        errReturn = errFindShortestPathLinear(pathInformation->posGetStart(), i32IdEnd, pathInformation->posGetEnd(), ptr_mipthDistanceMapStart, ptr_mipthDistanceMapEnd);

        if ((errReturn == errNoError) && (ptr_mipthDistanceMapStart->find(i32IdEnd) != ptr_mipthDistanceMapStart->end()))
        {
            (*pathInformation) = (*ptr_mipthDistanceMapStart)[i32IdEnd];
        }
        return (errReturn);
    }
    
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::enError CVisibilityGraph::errFindShortestPathLinear(const CPosition& posPositionStart, const CPosition& posPositionEnd, PTR_DEQUE_POSITION_t& ptr_dqposShortestPath)
    {
        enError errReturn(errNoError);
        int32_t i32IdEnd(1000); // dummy Id
        PTR_M_INT_PATHINFORMATION_t ptr_mipthDistanceMapStart(new M_INT_PATHINFORMATION_t);
        PTR_M_INT_PATHINFORMATION_t ptr_mipthDistanceMapEnd(new M_INT_PATHINFORMATION_t);

        errReturn = errFindShortestPathLinear(posPositionStart, i32IdEnd, posPositionEnd, ptr_mipthDistanceMapStart, ptr_mipthDistanceMapEnd);

        ptr_dqposShortestPath->clear();
        if ((errReturn == errNoError) && (ptr_mipthDistanceMapStart->find(i32IdEnd) != ptr_mipthDistanceMapStart->end()))
        {
            CPathInformation pthShortestPath = (*ptr_mipthDistanceMapStart)[i32IdEnd];
            if (pthShortestPath.iGetIndexBaseBegin() >= 0)
            {
                int iSanityCheck(static_cast<int> (vvvtxGetVertexParentBase()[pthShortestPath.iGetIndexBaseBegin()].size()));
                vertex_descriptor vtxBegin = static_cast<vertex_descriptor> (pthShortestPath.iGetIndexBaseBegin());
                vertex_descriptor vtxCurrent = vvvtxGetVertexParentBase()[pthShortestPath.iGetIndexBaseBegin()][pthShortestPath.iGetIndexBaseEnd()];
                while (vtxCurrent != vtxBegin)
                {
                    if (iSanityCheck >= 0)
                    {
                        ptr_dqposShortestPath->push_front(vposGetVerticiesBase()[vtxCurrent]);
                        vtxCurrent = vvvtxGetVertexParentBase()[pthShortestPath.iGetIndexBaseBegin()][vtxCurrent];
                    }
                    else
                    {
                        //error: did not find beginning of path
                        errReturn = errPathConstruction;
                        break;
                    }

                    iSanityCheck--;
                }
                ptr_dqposShortestPath->push_front(vposGetVerticiesBase()[vtxBegin]);
            } //if(pthShortestPath.iGetIndexBaseBegin() >= 0)
        }
        return (errReturn);
    }
    
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::enError CVisibilityGraph::errFindShortestPathLinear(const CPosition& posPositionStart,
            const int& iIdEnd, const CPosition& posPositionEnd,
            PTR_M_INT_PATHINFORMATION_t& ptr_mipthDistanceMapStart,
            PTR_M_INT_PATHINFORMATION_t& ptr_mipthDistanceMapEnd)
    {
        enError errReturn(errNoError);

        //////////////////////////////////////////////////////////////////////////////////////////
        // Check for visible edges from the FromPosition to the ToPosition
        //////////////////////////////////////////////////////////////////////////////////////////
        //CHECK TO SEE IF THERE IS A DIRECT PATH FROM START TO END

        // check for existing path
        if (ptr_mipthDistanceMapStart->find(iIdEnd) == ptr_mipthDistanceMapStart->end())
        {
            if (!bFindIntersection(vposGetVerticiesBase(), vplygnGetPolygons(), posPositionStart, posPositionEnd))
            {
                // NO INTERSECTIONS FOUND -> DIRECT PATH
                // that is it, we found a direct path
                (*ptr_mipthDistanceMapStart)[iIdEnd].iGetIndexBaseBegin() = -1;
                (*ptr_mipthDistanceMapStart)[iIdEnd].iGetIndexBaseEnd() = -1;
                (*ptr_mipthDistanceMapStart)[iIdEnd].iGetLength() = static_cast<int> (posPositionStart.relativeDistance2D_m(posPositionEnd));
                (*ptr_mipthDistanceMapStart)[iIdEnd].posGetStart() = posPositionStart;
                (*ptr_mipthDistanceMapStart)[iIdEnd].posGetEnd() = posPositionEnd;
            }
            else
            { // FIND A PATH ONTO THE BASE GRAPH
                //////////////////////////////////////////////////////////////////////////////////////////
                // Check for visible edges from the Start Position to all base vertices
                //////////////////////////////////////////////////////////////////////////////////////////

                CEdge edgeClosest;

                //check start position with all base vertices to find visible edges
                for (V_POLYGON_IT_t itPolygons1 = vplygnGetPolygons().begin(); itPolygons1 != (vplygnGetPolygons().end()); itPolygons1++)
                {
                    for (CEdge::V_EDGE_IT_t itEdge1 = itPolygons1->veGetPolygonEdges().begin(); itEdge1 != itPolygons1->veGetPolygonEdges().end(); itEdge1++)
                    {
                        // check to see if there is already a path
                        if (ptr_mipthDistanceMapStart->find(static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET) == ptr_mipthDistanceMapStart->end())
                        {
                            // no existing path, see if one exists
                            //    create line segments using vertices from current and existing
                            //    for each line segment check all polygon edges for intersections
                            if (!bFindIntersection(vposGetVerticiesBase(), vplygnGetPolygons(), posPositionStart, vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->first)], -1, static_cast<unsigned int> (itEdge1->first)))
                            {
                                int iVertexID = static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET;
                                (*ptr_mipthDistanceMapStart)[iVertexID].iGetIndexBaseBegin() = -1;
                                (*ptr_mipthDistanceMapStart)[iVertexID].iGetIndexBaseEnd() = static_cast<int> (itEdge1->first);
                                (*ptr_mipthDistanceMapStart)[iVertexID].iGetLength() = static_cast<int> (posPositionStart.relativeDistance2D_m(vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->first)]));
                                (*ptr_mipthDistanceMapStart)[iVertexID].posGetStart() = posPositionStart;
                                (*ptr_mipthDistanceMapStart)[iVertexID].posGetEnd() = vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->first)];
                            }
                        } //if (ptr_mipthDistanceMapStart->find(static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET;) == ptr_mipthDistanceMapStart->end())
                    } //for(CEdge::V_EDGE_IT_t itEdge1=itPolygons->veGetPolygonEdges().begin();itEdge1!=itPolygons->veGetPolygonEdges().end();itEdge1++)
                } //for(V_POLYGON_IT_t itPolygons1=vplygnGetPolygons().begin();itPolygons1!=(vplygnGetPolygons().end());itPolygons1++)

                //////////////////////////////////////////////////////////////////////////////////////////
                // Check for visible edges from all base vertices to the End Position
                //////////////////////////////////////////////////////////////////////////////////////////
                for (V_POLYGON_IT_t itPolygons1 = vplygnGetPolygons().begin(); itPolygons1 != (vplygnGetPolygons().end()); itPolygons1++)
                {
                    for (CEdge::V_EDGE_IT_t itEdge1 = itPolygons1->veGetPolygonEdges().begin(); itEdge1 != itPolygons1->veGetPolygonEdges().end(); itEdge1++)
                    {
                        // check to see if there is already a path
                        if (ptr_mipthDistanceMapEnd->find(static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET) == ptr_mipthDistanceMapEnd->end())
                        {
                            //    create line segments using vertices and the End Position
                            //    for each line segment check all polygon edges for intersections
                            if (!bFindIntersection(vposGetVerticiesBase(), vplygnGetPolygons(), vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->first)], posPositionEnd, static_cast<unsigned int> (itEdge1->first), -1))
                            {
                                int iVertexID = static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET;
                                (*ptr_mipthDistanceMapEnd)[iVertexID].iGetIndexBaseBegin() = static_cast<int> (itEdge1->first);
                                (*ptr_mipthDistanceMapEnd)[iVertexID].iGetIndexBaseEnd() = -1;
                                (*ptr_mipthDistanceMapEnd)[iVertexID].iGetLength() = static_cast<int> (posPositionEnd.relativeDistance2D_m(vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->first)]));
                                (*ptr_mipthDistanceMapEnd)[iVertexID].posGetStart() = vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->first)];
                                (*ptr_mipthDistanceMapEnd)[iVertexID].posGetEnd() = posPositionEnd;
                            }
                        } //if (ptr_mipthDistanceMapEnd->find(static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET) == ptr_mipthDistanceMapEnd->end())
                    } //for(CEdge::V_EDGE_IT_t itEdge1=itPolygons->veGetPolygonEdges().begin();itEdge1!=itPolygons->veGetPolygonEdges().end();itEdge1++)
                } //for(V_POLYGON_IT_t itPolygons1=vplygnGetPolygons().begin();itPolygons1!=(vplygnGetPolygons().end());itPolygons1++)
            } //if (!bInstersectionFound)
        } //if(ptr_mipthDistanceMapStart->find(iIdEnd) == ptr_mipthDistanceMapStart->end())  

        ////////////////////////////////////////////////////////////////////////////////////////////////////////////////                
        //Find the shortest path from the Start point To the End point
        //if visible edge exists from the START to the END, then we are done.
        if (ptr_mipthDistanceMapStart->find(iIdEnd) == ptr_mipthDistanceMapStart->end())
        {
            //no visible edge so continue
            // find the shortest path between the START and the End points
            // check all combinations of Start to base + base to base + base to End

            double dMinimumDistance((std::numeric_limits<double>::max)()); //set to big number
            CPathInformation pthiPathInformationMin; // save the min path parameters here

            for (auto itPathInfoStart = ptr_mipthDistanceMapStart->begin(); itPathInfoStart != ptr_mipthDistanceMapStart->end(); itPathInfoStart++)
            {
                if (itPathInfoStart->second.iGetIndexBaseBegin() == -1) //
                {
                    //Start Point to Base vertices
                    int iStartToBaseIndex(itPathInfoStart->second.iGetIndexBaseEnd());
                    //int iStartToBaseIndex(itPathInfoStart->second.iGetIndexBaseBegin());
                    if ((iStartToBaseIndex >= 0)&&(itPathInfoStart->second.iGetLength() >= 0))
                    {
                        // there is a visible edge between the Start Point and this base vertex
                        //Base vertices to End Point
                        for (auto itPathInfoEnd = ptr_mipthDistanceMapEnd->begin();
                                itPathInfoEnd != ptr_mipthDistanceMapEnd->end(); itPathInfoEnd++)
                        {
                            int iBaseToObjectiveIndex(itPathInfoEnd->second.iGetIndexBaseBegin());
                            if (iBaseToObjectiveIndex >= 0)
                            {
                                // there is a connection between the objective and this base vertex
                                double dDistanceCandidate =
                                        static_cast<double> (itPathInfoStart->second.iGetLength()) +
                                        static_cast<double> (vviGetVertexDistancesBase()[iStartToBaseIndex][iBaseToObjectiveIndex]) +
                                        static_cast<double> (itPathInfoEnd->second.iGetLength());

                                if (dDistanceCandidate < dMinimumDistance)
                                {
                                    dMinimumDistance = dDistanceCandidate;
                                    pthiPathInformationMin.iGetIndexBaseBegin() = iStartToBaseIndex;
                                    pthiPathInformationMin.iGetIndexBaseEnd() = iBaseToObjectiveIndex;
                                    pthiPathInformationMin.iGetLength() = static_cast<int> (dDistanceCandidate);
                                    pthiPathInformationMin.posGetStart() = itPathInfoStart->second.posGetStart();
                                    pthiPathInformationMin.posGetEnd() = itPathInfoEnd->second.posGetEnd();
                                }
                            }
                        } //for(size_t szIndexVertexBaseEnd=0;szIndexVertexBaseEnd<vviGetVertexDistancesBase()[szVehicleIndex].size();szIndexVertexBaseEnd++)
                    } //if(vviVisibleDistances[iIndexInMatrixVehicle][szIndexVertexBaseStart]>0)
                } //for(size_t szIndexVertexBaseStart=0;szIndexVertexBaseStart<vviGetVertexDistancesBase()[szVehicleIndex].size();szIndexVertexBaseStart++)
            } //if(itPathInfoStart->second.iGetIndexBaseBegin() == -1)    //
            (*ptr_mipthDistanceMapStart)[iIdEnd] = pthiPathInformationMin;
        } //if (ptr_mipthDistanceMapStart->find(iIdEnd) == ptr_mipthDistanceMapStart->end())
        return (errReturn);
    } //errAddVehicleObjectives


    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::enError CVisibilityGraph::errFindShortestPathGround(const CPosition& posPositionStart, const CPosition& posPositionEnd, PTR_DEQUE_POSITION_t& ptr_dqposShortestPath)
    {
        enError errReturn(errNoError);
        int32_t i32IdEnd(1000); // dummy Id
        PTR_M_INT_PATHINFORMATION_t ptr_mipthDistanceMapStart(new M_INT_PATHINFORMATION_t);
        PTR_M_INT_PATHINFORMATION_t ptr_mipthDistanceMapEnd(new M_INT_PATHINFORMATION_t);

        errReturn = errFindShortestPathGround(posPositionStart, i32IdEnd, posPositionEnd, ptr_mipthDistanceMapStart, ptr_mipthDistanceMapEnd);

        ptr_dqposShortestPath->clear();
        if ((errReturn == errNoError) && (ptr_mipthDistanceMapStart->find(i32IdEnd) != ptr_mipthDistanceMapStart->end()))
        {
            CPathInformation pthShortestPath = (*ptr_mipthDistanceMapStart)[i32IdEnd];
            if (pthShortestPath.iGetIndexBaseBegin() >= 0)
            {
                int iSanityCheck(static_cast<int> (vvvtxGetVertexParentBase()[pthShortestPath.iGetIndexBaseBegin()].size()));
                vertex_descriptor vtxBegin = static_cast<vertex_descriptor> (pthShortestPath.iGetIndexBaseBegin());
                vertex_descriptor vtxCurrent = vvvtxGetVertexParentBase()[pthShortestPath.iGetIndexBaseBegin()][pthShortestPath.iGetIndexBaseEnd()];
                while (vtxCurrent != vtxBegin)
                {
                    if (iSanityCheck >= 0)
                    {
                        ptr_dqposShortestPath->push_front(vposGetVerticiesBase()[vtxCurrent]);
                        vtxCurrent = vvvtxGetVertexParentBase()[pthShortestPath.iGetIndexBaseBegin()][vtxCurrent];
                    }
                    else
                    {
                        //error: did not find beginning of path
                        errReturn = errPathConstruction;
                        break;
                    }

                    iSanityCheck--;
                }
                ptr_dqposShortestPath->push_front(vposGetVerticiesBase()[vtxBegin]);
            } //if(pthShortestPath.iGetIndexBaseBegin() >= 0)
        }



        return (errReturn);
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    CVisibilityGraph::enError CVisibilityGraph::errFindShortestPathGround(const CPosition& posPositionStart,
            const int& iIdEnd, const CPosition& posPositionEnd,
            PTR_M_INT_PATHINFORMATION_t& ptr_mipthDistanceMapStart,
            PTR_M_INT_PATHINFORMATION_t& ptr_mipthDistanceMapEnd)
    {
        enError errReturn(errNoError);

        //////////////////////////////////////////////////////////////////////////////////////////
        // Check for visible edges from the FromPosition to the ToPosition
        //////////////////////////////////////////////////////////////////////////////////////////
        //CHECK TO SEE IF THERE IS A DIRECT PATH FROM START TO END

        // check for existing path
        if (ptr_mipthDistanceMapStart->find(iIdEnd) == ptr_mipthDistanceMapStart->end())
        {
            // FIND A PATH ONTO THE BASE GRAPH
            //////////////////////////////////////////////////////////////////////////////////////////
            // Check for visible edges from the Start Position to all base vertices
            //////////////////////////////////////////////////////////////////////////////////////////

            double dClosestEdge_m((std::numeric_limits<double>::max)()); //set to big number
            CEdge edgeClosest;

            //check start position with all base vertices to find visible edges
            for (auto itEdge1 = veGetEdgesVisibleBase().begin(); itEdge1 != veGetEdgesVisibleBase().end(); itEdge1++)
            {
                // check to see if there is already a path
                if (ptr_mipthDistanceMapStart->find(static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET) == ptr_mipthDistanceMapStart->end())
                {
                    //    create line segments using vertices from current and existing
                    double dDistanceToEdge_m = dDistanceFromPointToSegment(posPositionStart,
                            vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->first)],
                            vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->second)],
                            itEdge1->iGetLength());
                    if (dDistanceToEdge_m < dClosestEdge_m)
                    {
                        dClosestEdge_m = dDistanceToEdge_m;
                        edgeClosest = *itEdge1;
                    }
                } //if (ptr_mipthDistanceMapStart->find(static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET;) == ptr_mipthDistanceMapStart->end())
            } //for (auto itEdge=veGetEdgesVisibleBase().begin();itEdge!=veGetEdgesVisibleBase().end(); itEdge++)

            if (edgeClosest.first >= 0)
            {
                int iVertexID = static_cast<int> (edgeClosest.first) + BASE_VISIBILITY_ID_OFFSET;
                (*ptr_mipthDistanceMapStart)[iVertexID].iGetIndexBaseBegin() = -1;
                (*ptr_mipthDistanceMapStart)[iVertexID].iGetIndexBaseEnd() = static_cast<int> (edgeClosest.first);
                (*ptr_mipthDistanceMapStart)[iVertexID].iGetLength() = static_cast<int> (posPositionStart.relativeDistance2D_m(vposGetVerticiesBase()[static_cast<unsigned int> (edgeClosest.first)]));
                (*ptr_mipthDistanceMapStart)[iVertexID].posGetStart() = posPositionStart;
                (*ptr_mipthDistanceMapStart)[iVertexID].posGetEnd() = vposGetVerticiesBase()[static_cast<unsigned int> (edgeClosest.first)];
            }
#undef USE_BOTH_VERTICIES
#ifdef USE_BOTH_VERTICIES
            if (edgeClosest.second >= 0)
            {
                int iVertexID = static_cast<int> (edgeClosest.second) + BASE_VISIBILITY_ID_OFFSET;
                (*ptr_mipthDistanceMapStart)[iVertexID].iGetIndexBaseBegin() = -1;
                (*ptr_mipthDistanceMapStart)[iVertexID].iGetIndexBaseEnd() = static_cast<int> (edgeClosest.second);
                (*ptr_mipthDistanceMapStart)[iVertexID].iGetLength() = static_cast<int> (posPositionStart.relativeDistance2D_m(vposGetVerticiesBase()[static_cast<unsigned int> (edgeClosest.second)]));
                (*ptr_mipthDistanceMapStart)[iVertexID].posGetStart() = posPositionStart;
                (*ptr_mipthDistanceMapStart)[iVertexID].posGetEnd() = vposGetVerticiesBase()[static_cast<unsigned int> (edgeClosest.second)];
            }
#endif  //USE_BOTH_VERTICIES


            dClosestEdge_m = (std::numeric_limits<double>::max)(); //reset to big number
            edgeClosest = CEdge();

            //////////////////////////////////////////////////////////////////////////////////////////
            // Check for distance of edges from all base vertices to the End Position
            //////////////////////////////////////////////////////////////////////////////////////////
            for (auto itEdge1 = veGetEdgesVisibleBase().begin(); itEdge1 != veGetEdgesVisibleBase().end(); itEdge1++)
            {
                // check to see if there is already a path
                if (ptr_mipthDistanceMapEnd->find(static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET) == ptr_mipthDistanceMapEnd->end())
                {
                    //    create line segments using vertices from current and existing
                    double dDistanceToEdge_m = dDistanceFromPointToSegment(posPositionEnd,
                            vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->first)],
                            vposGetVerticiesBase()[static_cast<unsigned int> (itEdge1->second)],
                            itEdge1->iGetLength());
                    if (dDistanceToEdge_m < dClosestEdge_m)
                    {
                        dClosestEdge_m = dDistanceToEdge_m;
                        edgeClosest = *itEdge1;
                    }
                } //if (ptr_mipthDistanceMapStart->find(static_cast<int> (itEdge1->first) + BASE_VISIBILITY_ID_OFFSET;) == ptr_mipthDistanceMapStart->end())

            } //for (auto itEdge=veGetEdgesVisibleBase().begin();itEdge!=veGetEdgesVisibleBase().end(); itEdge++)
            if (edgeClosest.first >= 0)
            {
                int iVertexID = static_cast<int> (edgeClosest.first) + BASE_VISIBILITY_ID_OFFSET;
                (*ptr_mipthDistanceMapEnd)[iVertexID].iGetIndexBaseBegin() = static_cast<int> (edgeClosest.first);
                (*ptr_mipthDistanceMapEnd)[iVertexID].iGetIndexBaseEnd() = -1;
                (*ptr_mipthDistanceMapEnd)[iVertexID].iGetLength() = static_cast<int> (posPositionEnd.relativeDistance2D_m(vposGetVerticiesBase()[static_cast<unsigned int> (edgeClosest.first)]));
                (*ptr_mipthDistanceMapEnd)[iVertexID].posGetStart() = posPositionEnd;
                (*ptr_mipthDistanceMapEnd)[iVertexID].posGetEnd() = vposGetVerticiesBase()[static_cast<unsigned int> (edgeClosest.first)];
            }
#ifdef USE_BOTH_VERTICIES
            if (edgeClosest.second >= 0)
            {
                int iVertexID = static_cast<int> (edgeClosest.second) + BASE_VISIBILITY_ID_OFFSET;
                (*ptr_mipthDistanceMapEnd)[iVertexID].iGetIndexBaseBegin() = static_cast<int> (edgeClosest.second);
                (*ptr_mipthDistanceMapEnd)[iVertexID].iGetIndexBaseEnd() = -1;
                (*ptr_mipthDistanceMapEnd)[iVertexID].iGetLength() = static_cast<int> (posPositionEnd.relativeDistance2D_m(vposGetVerticiesBase()[static_cast<unsigned int> (edgeClosest.second)]));
                (*ptr_mipthDistanceMapEnd)[iVertexID].posGetStart() = posPositionEnd;
                (*ptr_mipthDistanceMapEnd)[iVertexID].posGetEnd() = vposGetVerticiesBase()[static_cast<unsigned int> (edgeClosest.second)];
            }
#endif  //USE_BOTH_VERTICIES

            ////////////////////////////////////////////////////////////////////////////////////////////////////////////////                
            //Find the shortest path from the Start point To the End point
            //if visible edge exists from the START to the END, then we are done.

            // find the shortest path between the START and the End points
            // check all combinations of Start to base + base to base + base to End

            double dMinimumDistance((std::numeric_limits<double>::max)()); //set to big number
            CPathInformation pthiPathInformationMin; // save the min path parameters here

            for (auto itPathInfoStart = ptr_mipthDistanceMapStart->begin(); itPathInfoStart != ptr_mipthDistanceMapStart->end(); itPathInfoStart++)
            {
                if (itPathInfoStart->second.iGetIndexBaseBegin() == -1) //
                {
                    //Start Point to Base vertices
                    int iStartToBaseIndex(itPathInfoStart->second.iGetIndexBaseEnd());
                    //int iStartToBaseIndex(itPathInfoStart->second.iGetIndexBaseBegin());
                    if ((iStartToBaseIndex >= 0)&&(itPathInfoStart->second.iGetLength() >= 0))
                    {
                        // there is a visible edge between the Start Point and this base vertex
                        //Base vertices to End Point
                        for (auto itPathInfoEnd = ptr_mipthDistanceMapEnd->begin(); itPathInfoEnd != ptr_mipthDistanceMapEnd->end(); itPathInfoEnd++)
                        {
                            int iBaseToObjectiveIndex(itPathInfoEnd->second.iGetIndexBaseBegin());
                            if (iBaseToObjectiveIndex >= 0)
                            {
                                // there is a connection between the objective and this base vertex
                                double dDistanceCandidate =
                                        static_cast<double> (itPathInfoStart->second.iGetLength()) +
                                        static_cast<double> (vviGetVertexDistancesBase()[iStartToBaseIndex][iBaseToObjectiveIndex]) +
                                        static_cast<double> (itPathInfoEnd->second.iGetLength());

                                if (dDistanceCandidate < dMinimumDistance)
                                {
                                    dMinimumDistance = dDistanceCandidate;
                                    pthiPathInformationMin.iGetIndexBaseBegin() = iStartToBaseIndex;
                                    pthiPathInformationMin.iGetIndexBaseEnd() = iBaseToObjectiveIndex;
                                    pthiPathInformationMin.iGetLength() = static_cast<int> (dDistanceCandidate);
                                    pthiPathInformationMin.posGetStart() = itPathInfoStart->second.posGetStart();
                                    pthiPathInformationMin.posGetEnd() = itPathInfoEnd->second.posGetEnd();
                                }
                            }
                        } //for(size_t szIndexVertexBaseEnd=0;szIndexVertexBaseEnd<vviGetVertexDistancesBase()[szVehicleIndex].size();szIndexVertexBaseEnd++)
                    } //if(vviVisibleDistances[iIndexInMatrixVehicle][szIndexVertexBaseStart]>0)
                } //for(size_t szIndexVertexBaseStart=0;szIndexVertexBaseStart<vviGetVertexDistancesBase()[szVehicleIndex].size();szIndexVertexBaseStart++)
            } //if(itPathInfoStart->second.iGetIndexBaseBegin() == -1)    //
            (*ptr_mipthDistanceMapStart)[iIdEnd] = pthiPathInformationMin;
        } //if(ptr_mipthDistanceMapStart->find(iIdEnd) == ptr_mipthDistanceMapStart->end())  
        return (errReturn);
    } //errAddVehicleObjectives

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

    bool CVisibilityGraph::isFindPath(std::shared_ptr<n_FrameworkLib::CPathInformation>& pathInformation)
    {
        bool isSuccessful(true);
        
        enError errReturn = errFindShortestPathLinear(pathInformation);
            
        isSuccessful = (errReturn == errNoError);
                
        return (isSuccessful);
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

#ifdef STEVETEST
    CVisibilityGraph::enError CVisibilityGraph::errAddVehicleObjectives(const int& iVehicleID, const CPosition& posVehiclePosition,
            M_PTR_I_OBJECTIVE_PARAMETERS_BASE_t& m_ptr_i_opGetObjectivesParameters,
            PTR_M_INT_PTR_M_INT_PATHINFORMATION_t& ptr_mipmipthLinearPathsToObjectives,
            const bool& bPlanToClosestEdge)
    {
        //TODO:: what to do about errors?????
        enError errReturn(errNoError);
        PRINT_DEBUG("*DEBUG*")

                // build matrix of distances for this vehicle to all objectives and from each objective to every other objective
                //I'm assuming that all vehicles and objectives have unique IDs (i.e. no vehicle or objective can have the same ID as any other vehicle or objective)

        (*ptr_mipmipthLinearPathsToObjectives)[iVehicleID] = PTR_M_INT_PATHINFORMATION_t(new M_INT_PATHINFORMATION_t);

        M_INT_PTR_M_INT_PATHINFORMATION_t mipmipthPathsToObjectives;

        for (auto itObjParameters1 = m_ptr_i_opGetObjectivesParameters.begin(); itObjParameters1 != m_ptr_i_opGetObjectivesParameters.end(); itObjParameters1++)
        {
            mipmipthPathsToObjectives[itObjParameters1->second->iGetID()] = PTR_M_INT_PATHINFORMATION_t(new M_INT_PATHINFORMATION_t);

            //CCA_CERR_FILE_LINE("iVehicleID[" << iVehicleID << "]")
            //CCA_CERR_FILE_LINE("itObjParameters1->second->iGetID()[" << itObjParameters1->second->iGetID() << "]")
            errReturn = errFindShortestPathLinear(posVehiclePosition, itObjParameters1->second->iGetID(), itObjParameters1->second->posGetStart(),
                                            (*ptr_mipmipthLinearPathsToObjectives)[iVehicleID],mipmipthPathsToObjectives[itObjParameters1->second->iGetID()]);
            
//            CCA_CERR_FILE_LINE("iVehicleID[" << iVehicleID << "] itObjParameters1->second->iGetID()[" << itObjParameters1->second->iGetID()
//                    << "] (*ptr_mipmipthLinearPathsToObjectives)[iVehicleID][iIdEnd].iGetLength()[" 
//                    << (*(*ptr_mipmipthLinearPathsToObjectives)[iVehicleID])[itObjParameters1->second->iGetID()].iGetLength() 
//                            << "] posVehiclePosition.m_north_m[" << posVehiclePosition.m_north_m << "] posVehiclePosition.m_east_m[" 
//                            << posVehiclePosition.m_east_m << "] itObjParameters1->second->posGetStart().m_north_m[" << itObjParameters1->second->posGetStart().m_north_m
//                            << "] itObjParameters1->second->posGetStart().m_east_m[" << itObjParameters1->second->posGetStart().m_east_m << "]")
            // find shortest path for objective1 to other objectives
            for (auto itObjParameters2 = m_ptr_i_opGetObjectivesParameters.begin(); itObjParameters2 != m_ptr_i_opGetObjectivesParameters.end(); itObjParameters2++)
            {
                if (itObjParameters1->second->iGetID() != itObjParameters2->second->iGetID())
                {
                    // find path for objective1 to objective2
                    if (ptr_mipmipthLinearPathsToObjectives->find(itObjParameters1->second->iGetID()) == ptr_mipmipthLinearPathsToObjectives->end())
                    {
                        (*ptr_mipmipthLinearPathsToObjectives)[itObjParameters1->second->iGetID()] = PTR_M_INT_PATHINFORMATION_t(new M_INT_PATHINFORMATION_t);
                    }
                    if (mipmipthPathsToObjectives.find(itObjParameters2->second->iGetID()) == mipmipthPathsToObjectives.end())
                    {
                        mipmipthPathsToObjectives[itObjParameters2->second->iGetID()] = PTR_M_INT_PATHINFORMATION_t(new M_INT_PATHINFORMATION_t);
                    }

                //CCA_CERR_FILE_LINE("itObjParameters2->second->iGetID()[" << itObjParameters2->second->iGetID() << "]")
                    errReturn = errFindShortestPathLinear(itObjParameters1->second->posGetEnd(), itObjParameters2->second->iGetID(), itObjParameters2->second->posGetStart(),
                            (*ptr_mipmipthLinearPathsToObjectives)[itObjParameters1->second->iGetID()],
                            mipmipthPathsToObjectives[itObjParameters2->second->iGetID()]);
                }
            }
        } //for(auto itObjParameters2=m_ptr_i_opGetObjectivesParameters.begin();itObjParameters2!=m_ptr_i_opGetObjectivesParameters.end();itObjParameters2++)

        return (errReturn);
    }
#endif  //#ifdef STEVETEST

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////        
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    

#ifdef STEVETEST
    CVisibilityGraph::enError CVisibilityGraph::errAddVehicleObjectivesGround(const int& iVehicleID, const CPosition& posVehiclePosition,
            M_PTR_I_OBJECTIVE_PARAMETERS_BASE_t& m_ptr_i_opGetObjectivesParameters,
            PTR_M_INT_PTR_M_INT_PATHINFORMATION_t& ptr_mipmipthLinearPathsToObjectives)
    {
        //TODO:: what to do aboout errors?????
        enError errReturn(errNoError);
        PRINT_DEBUG("*DEBUG*")

                // build matrix of distances for this vehicle to all objectives and from each objective to every other objective
                //I'm assuming that all vehicles and objectives have unique IDs (i.e. no vehicle or objective can have the same ID as any other vehicle or objective)

        if (ptr_mipmipthLinearPathsToObjectives->find(iVehicleID) == ptr_mipmipthLinearPathsToObjectives->end())
        {
            (*ptr_mipmipthLinearPathsToObjectives)[iVehicleID] = PTR_M_INT_PATHINFORMATION_t(new M_INT_PATHINFORMATION_t);
        }

        M_INT_PTR_M_INT_PATHINFORMATION_t mipmipthPathsToObjectives;

        for (auto itObjParameters1 = m_ptr_i_opGetObjectivesParameters.begin(); itObjParameters1 != m_ptr_i_opGetObjectivesParameters.end(); itObjParameters1++)
        {
            // find shortest path for vehicle to objective1
            if (mipmipthPathsToObjectives.find(itObjParameters1->second->iGetID()) == mipmipthPathsToObjectives.end())
            {
                mipmipthPathsToObjectives[itObjParameters1->second->iGetID()] = PTR_M_INT_PATHINFORMATION_t(new M_INT_PATHINFORMATION_t);
            }

            errReturn = errFindShortestPathGround(posVehiclePosition, itObjParameters1->second->iGetID(), itObjParameters1->second->posGetStart(),
                    (*ptr_mipmipthLinearPathsToObjectives)[iVehicleID],
                    mipmipthPathsToObjectives[itObjParameters1->second->iGetID()]);

            // find shortest path for objective1 to other objectives
            for (auto itObjParameters2 = m_ptr_i_opGetObjectivesParameters.begin(); itObjParameters2 != m_ptr_i_opGetObjectivesParameters.end(); itObjParameters2++)
            {
                if (itObjParameters1->second->iGetID() != itObjParameters2->second->iGetID())
                {
                    // find path for objective1 to objective2
                    if (ptr_mipmipthLinearPathsToObjectives->find(itObjParameters1->second->iGetID()) == ptr_mipmipthLinearPathsToObjectives->end())
                    {
                        (*ptr_mipmipthLinearPathsToObjectives)[itObjParameters1->second->iGetID()] = PTR_M_INT_PATHINFORMATION_t(new M_INT_PATHINFORMATION_t);
                    }
                    if (mipmipthPathsToObjectives.find(itObjParameters2->second->iGetID()) == mipmipthPathsToObjectives.end())
                    {
                        mipmipthPathsToObjectives[itObjParameters2->second->iGetID()] = PTR_M_INT_PATHINFORMATION_t(new M_INT_PATHINFORMATION_t);
                    }

                    errReturn = errFindShortestPathGround(itObjParameters1->second->posGetEnd(), itObjParameters2->second->iGetID(), itObjParameters2->second->posGetStart(),
                            (*ptr_mipmipthLinearPathsToObjectives)[itObjParameters1->second->iGetID()],
                            mipmipthPathsToObjectives[itObjParameters2->second->iGetID()]);
                }
            }
        } //for(auto itObjParameters2=m_ptr_i_opGetObjectivesParameters.begin();itObjParameters2!=m_ptr_i_opGetObjectivesParameters.end();itObjParameters2++)

        return (errReturn);
    }
#endif  //#ifdef STEVETEST

    ////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////

        bool CVisibilityGraph::isGenerateWaypoints(const std::shared_ptr<n_FrameworkLib::CPathInformation>& pathInformation,
                                                    const double& startingHeading_deg, const double& endingHeading_deg,
                                                    const double& turnRadius_m, const CTrajectoryParameters::enPathType_t& enpathType,const double& minimumWaypointSeparation_m,
                                                    std::vector<afrl::cmasi::Waypoint*>& planWaypoints)
        {
            bool isSuccessful(true);
            
            PlanningParameters planningParameters;
            
            planningParameters.positionBegin = pathInformation->posGetStart();
            planningParameters.m_headingBegin_rad = startingHeading_deg*n_Const::c_Convert::dDegreesToRadians();
            planningParameters.m_isStartHeadingValid = true;
                    
            planningParameters.positionEnd = pathInformation->posGetEnd();
            double endHeading_rad = (endingHeading_deg - 180.0)*n_Const::c_Convert::dDegreesToRadians();
            planningParameters.headingsToEndPoint.push_back(CHeadingParameters(endHeading_rad));
            
            planningParameters.m_waypointSeparationMin_m = minimumWaypointSeparation_m;
            planningParameters.m_turnRadius_m = turnRadius_m;
            planningParameters.m_pathType = enpathType;
            planningParameters.m_isFirstObjective = true;
            std::vector<CWaypoint> waypoints;
            
            enError error = errGenerateWaypoints(planningParameters,*pathInformation,waypoints);
            
            if(error == errNoError)
            {
                // convert waypoint to CMASI waypoints
                // convert waypoint positions to lat,long
                uxas::common::utilities::CUnitConversions flatEarth;
                for(auto waypoint : waypoints)
                {
                    double latitude_deg(0.0);
                    double longitude_deg(0.0);
                    flatEarth.ConvertNorthEast_mToLatLong_deg(
                            waypoint.m_north_m,
                            waypoint.m_east_m,
                            latitude_deg, longitude_deg);

                    //NOTE:: not setting AltitudeType, Number, NextWaypoint, Speed, SpeedType, ClimbRate, TurnType, VehicleActionList, ContingencyWaypointA, ContingencyWaypointB, AssociatedTasks
                    //NOTE:: only setting Latitude, Longitude, Altitude  :)
                    auto waypointCmasi = new afrl::cmasi::Waypoint();
                    waypointCmasi->setLatitude(latitude_deg);
                    waypointCmasi->setLongitude(longitude_deg);
                    waypointCmasi->setAltitude(waypoint.m_altitude_m);

                    planWaypoints.push_back(waypointCmasi);
                    waypointCmasi = nullptr; // gave up ownership
                }
            }
            else
            {
                isSuccessful = false;
            }
            return(isSuccessful);
        }
        
    ////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////

#ifdef STEVETEST
    CVisibilityGraph::enError CVisibilityGraph::errGenerateWaypoints(c_VehicleBase& cvbVehicle, c_ObjectiveParametersBase& cObjectiveParametersBase,
            PTR_M_INT_PTR_M_INT_PATHINFORMATION_t& ptr_mipmipthDistanceBasedOnLineSegments,
            const CTrajectoryParameters::enPathType_t enpathType, const bool bFirstObjective)
    {
        //CCA_CERR_FILE_LINE("FromTaskId[" << cvbVehicle.iGetLastTaskID() << "] ToTaskId[" << cObjectiveParametersBase.iGetID() << "]")
        enError errReturn(errNoError);
        if (ptr_mipmipthDistanceBasedOnLineSegments->find(cvbVehicle.iGetLastTaskID()) != ptr_mipmipthDistanceBasedOnLineSegments->end())
        {
            if (ptr_mipmipthDistanceBasedOnLineSegments->operator[](cvbVehicle.iGetLastTaskID())->find(cObjectiveParametersBase.iGetID()) != ptr_mipmipthDistanceBasedOnLineSegments->operator[](cvbVehicle.iGetLastTaskID())->end())
            {
                CPathInformation& pthifPath = (*ptr_mipmipthDistanceBasedOnLineSegments->operator[](cvbVehicle.iGetLastTaskID()))[cObjectiveParametersBase.iGetID()];
                errReturn = errGenerateWaypoints(cvbVehicle,cObjectiveParametersBase,pthifPath,enpathType,bFirstObjective);
            }
            else
            {
                CCA_CERR_FILE_LINE("ERRO::errGenerateWaypoints:: did not find the objective ID[" << cObjectiveParametersBase.iGetID() <<"] in the path information map");
                errReturn = errPathConstruction;
            }
        }
        else
        {
            //did not find the vehicle's last task ID position in the map
            CCA_CERR_FILE_LINE("ERRO::errGenerateWaypoints:: did not find vehicle's last task ID[" << cvbVehicle.iGetLastTaskID() <<"] in the path information map");
            errReturn = errPathConstruction;
        }
        
        return(errReturn);
    }
#endif  //#ifdef STEVETEST
        
    ////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////

    CVisibilityGraph::enError CVisibilityGraph::errGenerateWaypoints(const PlanningParameters& planningParameters,const CPathInformation& pthifPath,std::vector<CWaypoint>& waypoints)
    {
        //CCA_CERR_FILE_LINE("FromTaskId[" << cvbVehicle.iGetLastTaskID() << "] ToTaskId[" << cObjectiveParametersBase.iGetID() << "]")
        enError errReturn(errNoError);

        CBaseObject startObject(0,planningParameters.positionBegin.m_north_m,
                                                                planningParameters.positionBegin.m_east_m,
                                                                planningParameters.positionBegin.m_altitude_m,
                                                                planningParameters.m_headingBegin_rad);
        CTrajectory cTrajectory;
        // add Dubins path for beginning, from current Vehicle position to pthifPath.iGetIndexBaseBegin()
        if (pthifPath.iGetIndexBaseBegin() < 0)
        {
            // the path is from the vehicle directly to the objective
            CTrajectoryParameters cTrajectoryParameters;
            cTrajectoryParameters.trjGetParametersEnd().m_north_m = planningParameters.positionEnd.m_north_m;
            cTrajectoryParameters.trjGetParametersEnd().m_east_m = planningParameters.positionEnd.m_east_m;
            cTrajectoryParameters.trjGetParametersEnd().vGetHeadingParameters() = planningParameters.headingsToEndPoint;
            cTrajectoryParameters.trjGetParametersEnd().dGetStandOffNoHeadings_m() = planningParameters.m_StandOffNoHeadings;
            cTrajectoryParameters.dGetMinimumTime_s() = planningParameters.timePrerequsite_s;
            cTrajectoryParameters.dGetWaypointSeparationMin_m() = planningParameters.m_waypointSeparationMin_m;

            //CCA_CERR_FILE_LINE("Time[" << uxas::common::utilities::c_TimeUtilities::dGetTimeSinceStart_s() << "] cvbVehicle.m_north_m[" << cvbVehicle.m_north_m << "] cvbVehicle.m_east_m[" << cvbVehicle.m_east_m << "]")
            cTrajectoryParameters.bobjGetStart() = startObject;
            // check to see if we need to calculate the heading
            if (planningParameters.m_isFirstObjective && !planningParameters.m_isStartHeadingValid)
            {
                //heading from vehicle to the start point of the objective
                double dNewHeading_rad = n_Const::c_Convert::dPi() + n_Const::c_Convert::dPiO2() - planningParameters.positionBegin.relativeAngle2D_rad(planningParameters.positionEnd);
                cTrajectoryParameters.bobjGetStart().SetHeading(dNewHeading_rad);
            }

            cTrajectoryParameters.dGetAltitude_m() = planningParameters.positionBegin.m_altitude_m;
            cTrajectoryParameters.dGetSpeed_mps() = planningParameters.m_speed_mps;
            cTrajectoryParameters.dGetTurnRadius_m() = planningParameters.m_turnRadius_m;

            //cTrajectoryParameters.bGetLengthenPath() = true;
            cTrajectoryParameters.bGetLengthenPath() = false;
            cTrajectoryParameters.pathGetType() = planningParameters.m_pathType;
            cTrajectoryParameters.dGetWindHeadingFrom_rad() = 0.0;
            cTrajectoryParameters.dGetWindSpeed_mps() = 0.0;

            cTrajectory.dMinimumDistance(cTrajectoryParameters);

            CAssignment assignNew; //this is where the new path is stored
            for(auto& waypoint : cTrajectoryParameters.vGetWaypoints())
            {
                assignNew.iAddWaypoint(waypoint);
            }
            waypoints = assignNew.vwayGetWaypoints();

        }
        else //if(pthifPath.iGetIndexBaseBegin() < 0)
        {


            CAssignment assignNew; //this is where the new path is stored
            double dHeadingInitial_rad(0.0);
            bool bUseInitialHeading(false);
            
            //////////////////////////////////////////////////////
            // calculate a path from vehicle to the graph

            CTrajectoryParameters cTrajectoryParameters;
            cTrajectoryParameters.trjGetParametersEnd().iGetID() = 0;
            cTrajectoryParameters.trjGetParametersEnd().m_north_m = vposGetVerticiesBase()[pthifPath.iGetIndexBaseBegin()].m_north_m;
            cTrajectoryParameters.trjGetParametersEnd().m_east_m = vposGetVerticiesBase()[pthifPath.iGetIndexBaseBegin()].m_east_m;
            if(bUseInitialHeading)
            {
#ifdef STEVETEST
                cTrajectoryParameters.trjGetParametersEnd().vGetHeadingParameters().push_back(CHeadingParameters(dHeadingInitial_rad,0.0,0.0));
                cTrajectoryParameters.trjGetParametersEnd().vGetHeadingParameters().push_back(CHeadingParameters((dHeadingInitial_rad+n_Const::c_Convert::dPi()),0.0,0.0));
#endif  //STEVETEST
            }
            //cTrajectoryParameters.dGetMinimumTime_s() = (planningParameters.m_speed_mps <= 0.0) ? (0.0) : (0.0 / planningParameters.m_speed_mps);
            cTrajectoryParameters.dGetWaypointSeparationMin_m() = planningParameters.m_waypointSeparationMin_m;

            cTrajectoryParameters.bobjGetStart() = startObject;
            // check to see if we need to calculate the heading
            if (planningParameters.m_isFirstObjective && !planningParameters.m_isStartHeadingValid)
            {
                //heading from vehicle to the start point of the objective
                double dNewHeading_rad = n_Const::c_Convert::dPi() + n_Const::c_Convert::dPiO2() - startObject.relativeAngle2D_rad(vposGetVerticiesBase()[pthifPath.iGetIndexBaseBegin()]);
                cTrajectoryParameters.bobjGetStart().SetHeading(dNewHeading_rad);
            }

            cTrajectoryParameters.dGetAltitude_m() = planningParameters.positionBegin.m_altitude_m;
            cTrajectoryParameters.dGetSpeed_mps() = planningParameters.m_speed_mps;
            cTrajectoryParameters.dGetTurnRadius_m() = planningParameters.m_turnRadius_m;

            //cTrajectoryParameters.bGetLengthenPath() = true;
            cTrajectoryParameters.bGetLengthenPath() = false;
            cTrajectoryParameters.pathGetType() = planningParameters.m_pathType;
            cTrajectoryParameters.dGetWindHeadingFrom_rad() = 0.0;
            cTrajectoryParameters.dGetWindSpeed_mps() = 0.0;

            cTrajectory.dMinimumDistance(cTrajectoryParameters);

            // add the new waypoints to the vehicle
            for (V_WAYPOINT_IT_t itWaypoint = cTrajectoryParameters.vGetWaypoints().begin(); itWaypoint != cTrajectoryParameters.vGetWaypoints().end(); itWaypoint++)
            {
                assignNew.iAddWaypoint(*itWaypoint, true);
            }

            // need to account for adding a turn at the end of this segment. 
            // The segment terminates at the corner, but the turn starts before
            // the corner so need to remove the points that make up the corner. 
            if (assignNew.vwayGetWaypoints().size() > 1)
            {
                // path was generated as an attack. This adds 3 waypoints at the Objective.
                // just in case remove all the waypoints at the end at the same place
                CWaypoint Temp = assignNew.vwayGetWaypoints().back();
                Temp.iGetObjectiveID() = -1;
                Temp.typeGetWaypoint() = CWaypoint::waytypeEnroute;
                assignNew.vwayGetWaypoints().pop_back();
                assignNew.iAddWaypoint(Temp);
            }
            assignNew.vwayGetWaypoints().back().bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction

            //////////////////////////////////////////////////////
            /////////////////////////////////////////////////
            // construct a path based on the visibility graph
            /////////////////////////////////////////////////
            D_POSITION_t dposPathPositions;

            dposPathPositions.push_front(pthifPath.posGetEnd());

            CPosition posLastVertexBeforeObjective;

            if (pthifPath.iGetIndexBaseBegin() >= 0)
            {
                posLastVertexBeforeObjective = vposGetVerticiesBase()[static_cast<vertex_descriptor> (pthifPath.iGetIndexBaseEnd())];
                dposPathPositions.push_front(vposGetVerticiesBase()[static_cast<vertex_descriptor> (pthifPath.iGetIndexBaseEnd())]);

                int iSanityCheck(static_cast<int> (vvvtxGetVertexParentBase()[pthifPath.iGetIndexBaseBegin()].size()));
                vertex_descriptor vtxBegin = static_cast<vertex_descriptor> (pthifPath.iGetIndexBaseBegin());
                vertex_descriptor vtxCurrent = vvvtxGetVertexParentBase()[pthifPath.iGetIndexBaseBegin()][pthifPath.iGetIndexBaseEnd()];
                while (vtxCurrent != vtxBegin)
                {
                    if (iSanityCheck >= 0)
                    {
                        dposPathPositions.push_front(vposGetVerticiesBase()[vtxCurrent]);
                        vtxCurrent = vvvtxGetVertexParentBase()[pthifPath.iGetIndexBaseBegin()][vtxCurrent];
                    }
                    else
                    {
                        //error: did not find beginning of path
                        errReturn = errPathConstruction;
                        return (errReturn);
                    }

                    iSanityCheck--;
                }
                dposPathPositions.push_front(vposGetVerticiesBase()[vtxBegin]);
            }
            //dposPathPositions.push_front(pthifPath.posGetStart());

            //save visibility graph waypoints to the vehicle

            double dHeadingAfterSmoothing(0.0);
            if (planningParameters.m_pathType == CTrajectoryParameters::pathEuclidean)
            {
                CWaypoint wayWorking;
                wayWorking.iGetObjectiveID() = -1;
                wayWorking.typeGetWaypoint() = CWaypoint::waytypeEnroute;
                for (D_POSITION_IT_t itPosition = dposPathPositions.begin(); itPosition != dposPathPositions.end(); itPosition++)
                {
                    wayWorking.m_north_m = itPosition->m_north_m;
                    wayWorking.m_east_m = itPosition->m_east_m;
                    double dSegmentLength((assignNew.vwayGetWaypoints().empty()) ? (0.0) :
                            (assignNew.vwayGetWaypoints().back().relativeDistance2D_m(*itPosition)));
                    wayWorking.circleGetTurn() = CCircle((std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), CCircle::turnNone);
                    wayWorking.dGetSegmentLength() = dSegmentLength;
                    wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                    assignNew.iAddWaypoint(wayWorking);
                } //for(D_POSITION_IT_t itPosition;itPosition!=dposPathPositions.end();itPosition++)
            }
            else //if(enpathType==pathEuclidean)
            {
                errReturn = errSmoothPath(dposPathPositions, planningParameters.m_turnRadius_m,
                        dHeadingInitial_rad,dHeadingAfterSmoothing, assignNew.vwayGetWaypoints());
                bUseInitialHeading = true;
            } //if(enpathType==pathEuclidean)
            
            
            
            //////////////////////////////////////////////////////
             // add Dubins path for end, from ending pthifPath.iGetIndexBaseEnd() to cObjectiveParametersBase
            if (pthifPath.iGetIndexBaseEnd() >= 0)
            {
                // calculate vehicle to graph
                CTrajectoryParameters cTrajectoryParameters;
                cTrajectoryParameters.trjGetParametersEnd().m_north_m = planningParameters.positionEnd.m_north_m;
                cTrajectoryParameters.trjGetParametersEnd().m_east_m = planningParameters.positionEnd.m_east_m;
                cTrajectoryParameters.trjGetParametersEnd().vGetHeadingParameters() = planningParameters.headingsToEndPoint;
                cTrajectoryParameters.trjGetParametersEnd().dGetStandOffNoHeadings_m() = planningParameters.m_StandOffNoHeadings;
                cTrajectoryParameters.dGetMinimumTime_s() = planningParameters.timePrerequsite_s;
                cTrajectoryParameters.dGetWaypointSeparationMin_m() = planningParameters.m_waypointSeparationMin_m;
            

                auto lastWaypoint = assignNew.vwayGetWaypoints().back();
                cTrajectoryParameters.bobjGetStart() = CBaseObject(0,lastWaypoint.m_north_m,
                                                                lastWaypoint.m_east_m,
                                                                lastWaypoint.m_altitude_m,
                                                                dHeadingAfterSmoothing);

                cTrajectoryParameters.dGetAltitude_m() = planningParameters.positionBegin.m_altitude_m;
                cTrajectoryParameters.dGetSpeed_mps() = planningParameters.m_speed_mps;
                cTrajectoryParameters.dGetTurnRadius_m() = planningParameters.m_turnRadius_m;

                //cTrajectoryParameters.bGetLengthenPath() = true;
                cTrajectoryParameters.bGetLengthenPath() = false;
                cTrajectoryParameters.pathGetType() = planningParameters.m_pathType;
                cTrajectoryParameters.dGetWindHeadingFrom_rad() = 0.0;
                cTrajectoryParameters.dGetWindSpeed_mps() = 0.0;

                cTrajectory.dMinimumDistance(cTrajectoryParameters);

                // add the new waypoints to the vehicle
                for (V_WAYPOINT_IT_t itWaypoint = cTrajectoryParameters.vGetWaypoints().begin(); itWaypoint != cTrajectoryParameters.vGetWaypoints().end(); itWaypoint++)
                {
                    assignNew.iAddWaypoint(*itWaypoint, true);
                }
            }
            waypoints = assignNew.vwayGetWaypoints();
        } //if(pthifPath.iGetIndexBaseBegin() < 0)

        return (errReturn);
    }


    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    CVisibilityGraph::enError CVisibilityGraph::errSmoothPath(D_POSITION_t& dposPath, const double& dTurnRadius_m,
            double& dHeadingInitial_rad, double& dHeadingFinal_rad, V_WAYPOINT_t& vwayWaypoints)
    {
        //NOTE:: need to fix length of first waypoint to previous waypoint 
        enError errReturn(errNoError);

        // throw out "too short" segments
        bool bDone(false);
        while (!bDone)
        {
            bDone = true;
            auto itPosition1 = dposPath.begin();
            auto itPosition2 = itPosition1 + 1;
            for (; (itPosition1 != dposPath.end())&&(itPosition2 != dposPath.end()); itPosition1++, itPosition2++)
            {
                if (itPosition1->relativeDistance2D_m(*itPosition2) < iGetLengthSegmentMinimum())
                {
                    dposPath.erase(itPosition2);
                    bDone = false;
                    break;
                }
            }
        }

        CAssignment assignNew; //this is where the new path is stored

        //add enroute waypoints
        CWaypoint wayWorking;
        wayWorking.iGetObjectiveID() = -1;
        wayWorking.typeGetWaypoint() = CWaypoint::waytypeEnroute;

        double dHeadingAfterFinalSmoothing(0.0);
        bool bValidHeadingAfterSmoothing(false);
        
        bool isSmoothPath = false;
        
        if (!dposPath.empty())
        {
            // add the first vertex
            wayWorking.m_north_m = dposPath.front().m_north_m;
            wayWorking.m_east_m = dposPath.front().m_east_m;
            double dSegmentLength((assignNew.vwayGetWaypoints().empty()) ?
                    (0.0) :
                    (assignNew.vwayGetWaypoints().back().relativeDistance2D_m(dposPath.front())));
            wayWorking.circleGetTurn() = CCircle((std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), CCircle::turnNone);
            wayWorking.dGetSegmentLength() = dSegmentLength;
            wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
            assignNew.iAddWaypoint(wayWorking);
        }
        
        //% return if only one or two waypoints in the path
        if (dposPath.size() > 2)
        {
            //for p=2:(size(wp,1)-1),
            for (size_t szCountP = 1; szCountP < (dposPath.size() - 1); szCountP++)
            {
                //   % vector pointing from point P-1 to point P
                //     q1 = wp(p,:) - wp(p-1,:);   
                //   if norm(q1)==0,
                //       q1 = [0, 0];
                //   else
                //       q1 = q1./norm(q1);
                //   end;
                bValidHeadingAfterSmoothing = false;    // need to reset until last waypoint is added
                CPosition posQ1;
                posQ1 = dposPath[szCountP] - dposPath[szCountP - 1];
                double dNormQ1 = posQ1.absoluteDistance2D_m();
                if (n_Const::c_Convert::bCompareDouble(dNormQ1, 0.0, n_Const::c_Convert::enEqual))
                {
                    posQ1 = 0.0;
                }
                else
                {
                    posQ1 /= dNormQ1;
                }
                if(szCountP == 1)
                {
                    // calculate initial heading
                    dHeadingInitial_rad = n_Const::c_Convert::dPiO2() - dposPath[szCountP-1].relativeAngle2D_rad(dposPath[szCountP]);
                }
                //   % vector pointing from point P to point P+1
                //q2 = wp(p+1,:) - wp(p,:);
                //if norm(q2)==0,
                //    q2 = [0, 0];
                //else
                //    q2 = q2./norm(q2);
                //end;
                CPosition posQ2 = dposPath[szCountP + 1] - dposPath[szCountP];
                double dNormQ2 = posQ2.absoluteDistance2D_m();
                if (n_Const::c_Convert::bCompareDouble(dNormQ2, 0.0, n_Const::c_Convert::enEqual))
                {
                    posQ2 = 0.0;
                }
                else
                {
                    posQ2 /= dNormQ2;
                }

                //turn = turndir(q1,q2);
                CCircle::enTurnDirection_t enTurn = static_cast<CCircle::enTurnDirection_t> (static_cast<int> (turnDirection(posQ1, posQ2))); //turn = turndir(q1,q2);
                //beta = pi - acos(q1(1)*q2(1) + q1(2)*q2(2));
                double dBeta = n_Const::c_Convert::dPi();
                if (posQ1 != posQ2)
                {
                    dBeta = n_Const::c_Convert::dPi() - acos(posQ1.m_north_m * posQ2.m_north_m + posQ1.m_east_m * posQ2.m_east_m); //beta = pi - acos(q1(1)*q2(1) + q1(2)*q2(2));
                }

                //%if you're on a straight path don't create new points
                if (isSmoothPath && !n_Const::c_Convert::bCompareDouble(fabs(dBeta), n_Const::c_Convert::dPi(), n_Const::c_Convert::enEqual, n_Const::c_Convert::dDegreesToRadians()))
                {
                    //%If beta is less than 1 degree do a U-turn
                    if (dBeta < n_Const::c_Convert::dDegreesToRadians())
                    {
                        //c = getUturnCenter(wp(p,:),q2,R);
                        CPosition posC;
                        GetUTurnCenter(dposPath[szCountP], posQ2, dTurnRadius_m, posC);

                        //p1 = c + (R*sqrt(3))*q2;  % point closest to wp(p-1,:)
                        CPosition posP1(posC);
                        posP1 += posQ2 * dTurnRadius_m * sqrt(3.0);

                        //ct = (p1' + R*[0 -1; 1 0]*q2')';  %left hand rotation
                        CPosition posCt(posP1);
                        posCt += CPosition(-1 * posQ2.m_east_m, posQ2.m_north_m) * dTurnRadius_m;

                        //ce = (p1' + R*[0 1; -1 0]*q2')';  %right hand rotation
                        CPosition posCe(posP1);
                        posCe += CPosition(posQ2.m_east_m, -1 * posQ2.m_north_m) * dTurnRadius_m;

                        double dCosPiO3(cos(n_Const::c_Convert::dPi() / 3.0));
                        double dSinPiO3(cos(n_Const::c_Convert::dPi() / 3.0));

                        //p2 = (ct' + [cos(pi/3)  sin(pi/3); -sin(pi/3) cos(pi/3)]*(p1-ct)')'; % right rotate by pi/3
                        CPosition posP2(posCt);
                        CPosition posTemp(posP1);
                        posTemp -= posCt;
                        posP2 += CPosition((dCosPiO3 * posTemp.m_north_m) + (dSinPiO3 * posTemp.m_east_m),
                                (-dSinPiO3 * posTemp.m_north_m) + (dCosPiO3 * posTemp.m_east_m));

                        //p3 = (ce' + [cos(pi/3) -sin(pi/3);  sin(pi/3) cos(pi/3)]*(p1-ce)')'; % left rotate by pi/3
                        CPosition posP3(posCe);
                        posTemp = posP1;
                        posTemp -= posCe;
                        posP3 += CPosition((dCosPiO3 * posTemp.m_north_m) - (dSinPiO3 * posTemp.m_east_m),
                                (dSinPiO3 * posTemp.m_north_m) + (dCosPiO3 * posTemp.m_east_m));
                        //p4 = p1;
                        CPosition posP4(posP1);

                        //add enroute waypoints

                        //
                        //swp = [swp; [p1 norm(p1-swp(end,1:2)) p1 0]; [p2 pi/3*R ct -1]; [p3 5*pi/3*R c 1]; [p4 pi/3*R ce -1]];
                        //[p1 norm(p1-swp(end,1:2)) p1 0]
                        wayWorking.m_north_m = posP1.m_north_m;
                        wayWorking.m_east_m = posP1.m_east_m;
                        double dSegmentLength((assignNew.vwayGetWaypoints().empty()) ?
                                (0.0) :
                                (assignNew.vwayGetWaypoints().back().relativeDistance2D_m(posP1)));
                        wayWorking.dGetSegmentLength() = dSegmentLength;
                        wayWorking.circleGetTurn() = CCircle((std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), CCircle::turnNone);
                        wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                        assignNew.iAddWaypoint(wayWorking);

                        //[p2 pi/3*R ct -1]
                        wayWorking.m_north_m = posP1.m_north_m;
                        wayWorking.m_east_m = posP1.m_east_m;
                        wayWorking.dGetSegmentLength() = n_Const::c_Convert::dPi() / 3.0 * dTurnRadius_m;
                        wayWorking.circleGetTurn() = posCt;
                        //wayWorking.turnGetTurnDirection() = CCircle::turnClockwise;
                        wayWorking.turnGetTurnDirection() = CCircle::turnCounterclockwise;
                        wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                        assignNew.iAddWaypoint(wayWorking);

                        //[p3 5*pi/3*R c 1]
                        wayWorking.m_north_m = posP1.m_north_m;
                        wayWorking.m_east_m = posP1.m_east_m;
                        wayWorking.dGetSegmentLength() = 5.0 * n_Const::c_Convert::dPi() / 3.0 * dTurnRadius_m;
                        wayWorking.circleGetTurn() = posC;
                        //wayWorking.turnGetTurnDirection() = CCircle::turnCounterclockwise;
                        wayWorking.turnGetTurnDirection() = CCircle::turnClockwise;
                        wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                        assignNew.iAddWaypoint(wayWorking);

                        //[p4 pi/3*R ce -1]]
                        wayWorking.m_north_m = posP1.m_north_m;
                        wayWorking.m_east_m = posP1.m_east_m;
                        wayWorking.dGetSegmentLength() = n_Const::c_Convert::dPi() / 3.0 * dTurnRadius_m;
                        wayWorking.circleGetTurn() = posCe;
                        //wayWorking.turnGetTurnDirection() = CCircle::turnClockwise;
                        wayWorking.turnGetTurnDirection() = CCircle::turnCounterclockwise;
                        wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                        assignNew.iAddWaypoint(wayWorking);
                    }
                    else //if(dBeta < n_Const::c_Convert::dDegreesToRadians())
                    {
                        //switch kappa,
                        //    case 0,    % pass directly over waypoint
                        //        kap = 0;
                        //    case 1,    % shortest path
                        //        kap = 1;
                        //    otherwise, % equal path length
                        //        kap = GetKappa(R,beta,30);
                        //end;

                        double dKap(0.0);
                        switch (ptypeGetType())
                        {
                            default:
                            case CPathInformation::ptypeFlyOverWaypoint:
                                dKap = 0.0;
                                break;
                            case CPathInformation::ptypeShortestPath:
                                dKap = 1.0;
                                break;
                            case CPathInformation::ptypeEqualLength:
                                dKap = dGetKappa(dTurnRadius_m, dBeta, 30);
                                break;
                        }


                        //c = getturncenter(wp(p,:),q1,q2,R,kap,beta);
                        CPosition posC;
                        GetTurnCenter(dposPath[szCountP], posQ1, posQ2, dTurnRadius_m, dKap, dBeta, posC);

                        //switch kappa,
                        switch (ptypeGetType())
                        {
                            case CPathInformation::ptypeShortestPath:
                            {
                                //    case 1,    % shortest path - only one segment
                                //        d = sqrt( norm(wp(p,:) - c)^2 - R^2 );
                                CPosition posTemp(dposPath[szCountP]);
                                posTemp -= posC;
                                double dD(sqrt(pow(posTemp.absoluteDistance2D_m(), 2.0) - pow(dTurnRadius_m, 2.0)));

                                //        a = wp(p,:) - q1*d; % point closest to wp(p-1,:)
                                CPosition posA(dposPath[szCountP]);
                                posA -= posQ1*dD;

                                //        z = wp(p,:) + q2*d; % point closest to wp(p+1,:)
                                CPosition posZ(dposPath[szCountP]);
                                posZ += posQ2*dD;

                                //        gam = acos( (norm(a - z)^2 - 2*R^2)/(-2*R^2) );
                                posTemp = posA;
                                posTemp -= posZ;

                                //        swp = [swp; [a norm(swp(end,1:2)-a) a 0]; [z R*gam c turn]];
                                //
                                //[a norm(swp(end,1:2)-a) a 0]
                                wayWorking.m_north_m = posA.m_north_m;
                                wayWorking.m_east_m = posA.m_east_m;
                                double dSegmentLength((assignNew.vwayGetWaypoints().empty()) ?
                                        (0.0) :
                                        (assignNew.vwayGetWaypoints().back().relativeDistance2D_m(posA)));
                                wayWorking.dGetSegmentLength() = dSegmentLength;
                                wayWorking.circleGetTurn() = CCircle((std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), CCircle::turnNone);
                                assignNew.iAddWaypoint(wayWorking);

                                //[z R*gam c turn]
                                wayWorking.m_north_m = posZ.m_north_m;
                                wayWorking.m_east_m = posZ.m_east_m;
                                wayWorking.dGetSegmentLength() = n_Const::c_Convert::dPi() / 3.0 * dTurnRadius_m;
                                wayWorking.circleGetTurn() = posC;
                                //wayWorking.turnGetTurnDirection() = enTurn;
                                wayWorking.turnGetTurnDirection() = static_cast<CCircle::enTurnDirection_t> (-static_cast<int> (enTurn));
                                //                            wayWorking.turnGetTurnDirection() = static_cast<CCircle::enTurnDirection_t>(static_cast<int>(enTurn));
                                wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                                assignNew.iAddWaypoint(wayWorking);
                                //calculate the final heading of this curve
                                dHeadingAfterFinalSmoothing = atan2((wayWorking.m_east_m - posC.m_east_m), (wayWorking.m_north_m - posC.m_north_m));
                                dHeadingAfterFinalSmoothing += (wayWorking.turnGetTurnDirection() == CCircle::turnClockwise) ? (n_Const::c_Convert::dPiO2()) : (-n_Const::c_Convert::dPiO2());
                                bValidHeadingAfterSmoothing = true;
                            }
                                break;
                            default:
                            case CPathInformation::ptypeEqualLength:
                            case CPathInformation::ptypeFlyOverWaypoint:
                            {
                                //    otherwise, % equal length path or through waypoint - 3 segments

                                //        % rotate to vertical
                                //        th = atan2(q1(2),q1(1)) - pi/2;
                                double dTh = atan2(posQ1.m_east_m, posQ1.m_north_m) - n_Const::c_Convert::dPiO2();

                                //        [d, ct] = twoturndist( turn*R, [cos(th) sin(th); -sin(th) cos(th)]*((c-wp(p,:))') );
                                double dTempR(static_cast<int> (enTurn) * dTurnRadius_m);
                                CPosition posTemp(posC);
                                posTemp -= dposPath[szCountP];
                                CPosition posTemp1((cos(dTh) * posTemp.m_north_m + sin(dTh) * posTemp.m_east_m),
                                        (-sin(dTh) * posTemp.m_north_m + cos(dTh) * posTemp.m_east_m));

                                double dD;
                                CPosition posCt;
                                TwoTurnDist(dTempR, posTemp1, dD, posCt);

                                //        ct = ct*[cos(th) sin(th); -sin(th) cos(th)] + wp(p,:);
                                posTemp.m_north_m = cos(dTh) * posCt.m_north_m - sin(dTh) * posCt.m_east_m;
                                posTemp.m_east_m = sin(dTh) * posCt.m_north_m + cos(dTh) * posCt.m_east_m;
                                posCt = posTemp + dposPath[szCountP];

                                //        % use law of cosines
                                //        t = 2*R;
                                double dT(2.0 * dTurnRadius_m);

                                //        u = d/cos(beta/2) - norm(wp(p,:)-c);
                                posTemp = dposPath[szCountP] - posC;
                                double dCosBetaO2 = cos(dBeta / 2.0);
                                double dU(0.0);
                                if (!n_Const::c_Convert::bCompareDouble(dCosBetaO2, 0.0, n_Const::c_Convert::enEqual))
                                {
                                    dU = dD / cos(dBeta / 2.0) - posTemp.absoluteDistance2D_m();
                                }
                                else
                                {
                                    //TODO:: is this an error???
                                    dU = (std::numeric_limits<double>::max)();
                                }

                                //        v = R + d*tan(beta/2);
                                double dV(dTurnRadius_m + dD * tan(dBeta / 2.0));

                                //        gam1 = acos( (-u^2 + t^2 + v^2)/(2*t*v) );
                                double dGam1(acos((-pow(dU, 2.0) + pow(dT, 2.0) + pow(dV, 2.0)) / (2.0 * dT * dV)));

                                //        gam2 = 2*pi - 2*acos( (-v^2 + t^2 + u^2)/(2*t*u) );
                                double dGam2(2.0 * n_Const::c_Convert::dPi() - 2.0 * acos((-pow(dV, 2.0) + pow(dT, 2.0) + pow(dU, 2.0)) / (2.0 * dT * dU)));

                                //        a = wp(p,:) - q1*d; % point closest to wp(p-1,:)
                                CPosition posA = dposPath[szCountP] - posQ1*dD;

                                //        b = ct + (a - ct)*[cos(gam1) -sin(turn*gam1); sin(turn*gam1) cos(gam1)];
                                posTemp1 = posA - posCt;
                                posTemp.m_north_m = cos(dGam1) * posTemp1.m_north_m + sin(static_cast<int> (enTurn) * dGam1) * posTemp1.m_east_m;
                                posTemp.m_east_m = -sin(static_cast<int> (enTurn) * dGam1) * posTemp1.m_north_m + cos(dGam1) * posTemp1.m_east_m;
                                CPosition posB = posCt + posTemp;

                                //        y = c + (b - c)*[cos(gam2) sin(turn*gam2); -sin(turn*gam2) cos(gam2)];
                                posTemp1 = posB - posC;
                                posTemp.m_north_m = cos(dGam2) * posTemp1.m_north_m - sin(static_cast<int> (enTurn) * dGam2) * posTemp1.m_east_m;
                                posTemp.m_east_m = sin(static_cast<int> (enTurn) * dGam2) * posTemp1.m_north_m + cos(dGam2) * posTemp1.m_east_m;
                                CPosition posY(posC + posTemp);

                                //        z = wp(p,:) + q2*d; % point closest to wp(p+1,:)
                                CPosition posZ(dposPath[szCountP] + posQ2 * dD);

                                //        ce = c + (ct - c)*[cos(gam2) sin(turn*gam2); -sin(turn*gam2) cos(gam2)];
                                posTemp1 = posCt - posC;
                                posTemp.m_north_m = cos(dGam2) * posTemp1.m_north_m - sin(static_cast<int> (enTurn) * dGam2) * posTemp1.m_east_m;
                                posTemp.m_east_m = sin(static_cast<int> (enTurn) * dGam2) * posTemp1.m_north_m + cos(dGam2) * posTemp1.m_east_m;
                                CPosition posCe(posC + posTemp);

                                //        swp = [swp; [a norm(swp(end,1:2)-a) a 0]; [b R*gam1 ct -turn]; [y R*gam2 c turn]; [z R*gam1 ce -turn]];
                                //[a norm(swp(end,1:2)-a) a 0]
                                wayWorking.m_north_m = posA.m_north_m;
                                wayWorking.m_east_m = posA.m_east_m;
                                double dSegmentLength((assignNew.vwayGetWaypoints().empty()) ?
                                        (0.0) :
                                        (assignNew.vwayGetWaypoints().back().relativeDistance2D_m(posA)));
                                wayWorking.circleGetTurn() = CCircle((std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), CCircle::turnNone);
                                wayWorking.dGetSegmentLength() = dSegmentLength;
                                wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                                assignNew.iAddWaypoint(wayWorking);

                                //[b R*gam1 ct -turn]
                                wayWorking.m_north_m = posB.m_north_m;
                                wayWorking.m_east_m = posB.m_east_m;
                                wayWorking.dGetSegmentLength() = dTurnRadius_m*dGam1;
                                wayWorking.circleGetTurn() = posCt;
                                //wayWorking.turnGetTurnDirection() = static_cast<CCircle::enTurnDirection_t>(-static_cast<int>(enTurn));
                                wayWorking.turnGetTurnDirection() = static_cast<CCircle::enTurnDirection_t> (static_cast<int> (enTurn));
                                wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                                assignNew.iAddWaypoint(wayWorking);

                                //[y R*gam2 c turn]
                                wayWorking.m_north_m = posY.m_north_m;
                                wayWorking.m_east_m = posY.m_east_m;
                                wayWorking.dGetSegmentLength() = dTurnRadius_m*dGam2;
                                wayWorking.circleGetTurn() = posC;
                                //wayWorking.turnGetTurnDirection() = enTurn;
                                wayWorking.turnGetTurnDirection() = static_cast<CCircle::enTurnDirection_t> (-static_cast<int> (enTurn));
                                wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                                assignNew.iAddWaypoint(wayWorking);

                                //[z R*gam1 ce -turn]
                                wayWorking.m_north_m = posZ.m_north_m;
                                wayWorking.m_east_m = posZ.m_east_m;
                                wayWorking.dGetSegmentLength() = dTurnRadius_m*dGam1;
                                wayWorking.circleGetTurn() = posCe;
                                //wayWorking.turnGetTurnDirection() = static_cast<CCircle::enTurnDirection_t>(-static_cast<int>(enTurn));
                                wayWorking.turnGetTurnDirection() = static_cast<CCircle::enTurnDirection_t> (static_cast<int> (enTurn));
                                wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                                assignNew.iAddWaypoint(wayWorking);

                                //calculate the final heading of this curve
                                dHeadingAfterFinalSmoothing = atan2((wayWorking.m_east_m - posCe.m_east_m), (wayWorking.m_north_m - posCe.m_north_m));
                                dHeadingAfterFinalSmoothing += (wayWorking.turnGetTurnDirection() == CCircle::turnClockwise) ? (n_Const::c_Convert::dPiO2()) : (-n_Const::c_Convert::dPiO2());
                                bValidHeadingAfterSmoothing = true;
                            }
                                break;
                        }

                    } //if(dBeta < n_Const::c_Convert::dDegreesToRadians())
                }
                else //if(dBeta<n_Const::c_Convert::dPi())
                {
                    //swp = [swp; [wp(p,:) norm(swp(end,1:2) - wp(p,:)) wp(p,:) 0]];
                    //[wp(p,:) norm(swp(end,1:2) - wp(p,:)) wp(p,:) 0]
                    wayWorking.m_north_m = dposPath[szCountP].m_north_m;
                    wayWorking.m_east_m = dposPath[szCountP].m_east_m;
                    double dSegmentLength((assignNew.vwayGetWaypoints().empty()) ?
                            (0.0) :
                            (assignNew.vwayGetWaypoints().back().relativeDistance2D_m(dposPath[szCountP])));
                    wayWorking.circleGetTurn() = CCircle((std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), (std::numeric_limits<double>::max)(), CCircle::turnNone);
                    wayWorking.dGetSegmentLength() = dSegmentLength;
                    wayWorking.bGetDoNotRemove() = true; //don't let this waypoint be removed during waypoint reduction
                    assignNew.iAddWaypoint(wayWorking);
                } //if(dBeta<n_Const::c_Convert::dPi())
            } //for(size_t szCountP=1;szCountP<(dposPath.size()-1);szCountP)
        } //if(dposPath.size() > 2)

        // find the final heading
        dHeadingFinal_rad = 0.0;
        if (assignNew.vwayGetWaypoints().size() >= 1)
        {
            if (!bValidHeadingAfterSmoothing)
            {
                dHeadingFinal_rad = assignNew.dCalculateFinalHeading_rad();
            }
            else
            {
                dHeadingFinal_rad = dHeadingAfterFinalSmoothing;
            }
        }
        // add the new waypoints
        for (V_WAYPOINT_IT_t itWaypoint = assignNew.vwayGetWaypoints().begin(); itWaypoint != assignNew.vwayGetWaypoints().end(); itWaypoint++)
        {
            vwayWaypoints.push_back(*itWaypoint);
        }
        return (errReturn);
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////

    ostream &operator<<(ostream &os, const CVisibilityGraph& visgRhs)
    {

#ifdef MATALB_PLOTS
        os << "[";
        for (CEdge::V_EDGE_CONST_IT_t itEdge = visgRhs.veGetEdgesVisibleBase().begin(); itEdge != visgRhs.veGetEdgesVisibleBase().end(); itEdge++)
        {
            os << "[";
            os << visgRhs.vposGetVerticiesBase()[static_cast<unsigned int> (itEdge->first)];
            os << ",";
            os << visgRhs.vposGetVerticiesBase()[static_cast<unsigned int> (itEdge->second)];
            os << ",";
            os << itEdge->iGetLength();
            os << "]" << std::endl;
            ;
        }
        os << "]";
        return os;
#else    //#ifdef MATALB_PLOTS
        for (CEdge::V_EDGE_CONST_IT_t itEdge = visgRhs.veGetEdgesVisibleBase().begin(); itEdge != visgRhs.veGetEdgesVisibleBase().end(); itEdge++)
        {
            os << itEdge->first;
            os << ",";
            os << visgRhs.vposGetVerticiesBase()[static_cast<unsigned int> (itEdge->first)];
            os << ",";
            os << itEdge->second;
            os << ",";
            os << visgRhs.vposGetVerticiesBase()[static_cast<unsigned int> (itEdge->second)];
            os << ",";
            os << itEdge->iGetLength();
            os << std::endl;
            ;
        }
        return os;
#endif    //#ifdef MATALB_PLOTS
    }


}; //namespace n_FrameworkLib
