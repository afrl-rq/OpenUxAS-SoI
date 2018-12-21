// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   Component_OSM_Planner.h
 * Author: steve
 *
 * Created on September 25, 2015, 4:47 PM
 */

#ifndef UXAS_SERVICE_OSM_PLANNER_SERVICE_H
#define UXAS_SERVICE_OSM_PLANNER_SERVICE_H

#include "Position.h"
#include "Edge.h"


#include "VisibilityGraph.h"
#include "FlatEarth.h"

#include "ServiceBase.h"
#include "Constants/Constants_Control.h"

#include "uxas/messages/route/RoutePlanRequest.h"
#include "uxas/messages/route/RoutePlanResponse.h"
#include "uxas/messages/route/EgressRouteRequest.h"
#include "uxas/messages/route/EgressRouteResponse.h"
#include "uxas/messages/route/RoadPointsRequest.h"
#include "uxas/messages/route/RoadPointsResponse.h"

#include "boost/graph/astar_search.hpp"
#include "boost/graph/graph_traits.hpp"
#include "boost/graph/adjacency_list.hpp"

#include <unordered_map>

namespace uxas
{
namespace service
{

/*! \class OsmPlannerService
    \brief A service that loads an Open Street Map file, and constructs ground plans/costs to be used for assignments.

 * 1) Receive KeepInZones/KeepOutZones/Tasks/RoutePlanRequests
 * 2) Build/Maintain Base Visibility Graph (Euclidean) from KeepInZones/KeepOutZones
 * 3) ???Construct, and send out, a RoutePlanResponse which includes minimum
 *    path lengths from each vehicle to each task and from each task to every other task.?????
 * 4) ???Construct, and send out, a ???Response which includes minimum waypoint paths
 *    paths for each plan request.?????
 * 
 * Configuration String: 
 *  <Service Type="OsmPlannerService" OsmFile="" MapEdgesFile=""  ShortestPathFile=""  MetricsFile="" />
 * 
 * Options:
 *  - OsmFile
 *  - MapEdgesFile
 *  - ShortestPathFile
 *  - MetricsFile
 * 
 * Subscribed Messages:
 *  - GroundPathPlanner
 *  - afrl::vehicles::GroundVehicleConfiguration
 *  - uxas::messages::route::EgressRouteRequest
 *  - uxas::messages::route::RoutePlanRequest
 * 
 * Sent Messages:
 *  - uxas::messages::route::RoutePlanResponse
 *  - uxas::messages::route::EgressRouteResponse
 * 
 */


class OsmPlannerService : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("OsmPlannerService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };
    
    static const std::string&
    s_directoryName()
    {
        static std::string s_string("");
        return (s_string);
    };

    static ServiceBase*
    create()
    {
        return new OsmPlannerService;
    };

    OsmPlannerService();

    virtual
    ~OsmPlannerService();

private:

    static
    ServiceBase::CreationRegistrar<OsmPlannerService> s_registrar;

    /** brief Copy construction not permitted */
    OsmPlannerService(OsmPlannerService const&) = delete;

    /** brief Copy assignment operation not permitted */
    void operator=(OsmPlannerService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;

    bool
    initialize() override;

    //bool
    //start() override;

    //bool
    //terminate() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


public:
    //TODO:: is boost::vecS faster than boost::listS ???
    //using Graph_t = boost::adjacency_list < boost::vecS, boost::vecS, boost::undirectedS, boost::no_property, boost::property < boost::edge_weight_t, int32_t > >;
    using Graph_t = boost::adjacency_list < boost::listS, boost::vecS, boost::undirectedS, boost::no_property, boost::property < boost::edge_weight_t, int32_t > >;
    using VertexDescriptor_t = boost::graph_traits <Graph_t>::vertex_descriptor;
    using EdgeDescriptor_t = boost::graph_traits<Graph_t>::edge_descriptor;

public:



public: //virtual





public:

    struct PairIdHash
    {
        typedef std::pair<int64_t, int64_t> argument_type;
        typedef std::size_t result_type;

        result_type operator()(argument_type const& s) const
        {
            result_type const h1(std::hash<int64_t>()(s.first));
            result_type const h2(std::hash<int64_t>()(s.second));
            result_type returnValue = h1 ^ (h2 << 1);
            //std::cout << "Hash[" << returnValue << "] s.first[" << s.first << "] s.second[" << s.second << "]" << std::endl;
            return returnValue;
        }
    };


protected:
    bool bProcessRoutePlanRequest(const std::shared_ptr<uxas::messages::route::RoutePlanRequest>& routePlanRequest,
            std::shared_ptr<uxas::messages::route::RoutePlanResponse>& routePlanResponse);
    bool bProcessEgressRequest(const std::shared_ptr<uxas::messages::route::EgressRouteRequest>& egressRequest,
            std::shared_ptr<uxas::messages::route::EgressRouteResponse>& egressResponse);
    bool isProcessRoadPointsRequest(const std::shared_ptr<uxas::messages::route::RoadPointsRequest>& roadPointsRequest,
                                    std::shared_ptr<uxas::messages::route::RoadPointsResponse>& roadPointsResponse);
    bool isGetRoadPoints(const int64_t& startNodeId,const int64_t& endNodeId,int32_t& pathCost,std::deque<int64_t>& pathNodeIds);
    bool isBuildRoadGraphWithOsm(const string& osmFile);
    bool isFindShortestRoute(const int64_t& startNodeId, const int64_t& endNodeId,
            int32_t& pathCost, std::deque<int64_t>& pathNodes);
    bool isProcessHighwayNodes(const std::unordered_map<int64_t, bool>& nodeIdVs_isPlanningNode,
            const std::vector<int64_t>& highWayIds);
    bool isBuildGraph(const std::unordered_set<int64_t>& planningNodeIds, const std::vector<int64_t>& highWayIds);
    bool isFindClosestNodeId(const n_FrameworkLib::CPosition& position,
                             std::unordered_multimap<std::pair<int32_t, int32_t>, int64_t, PairIdHash >& cellVsNodeIds,
                             int64_t& nodeId, double& length_m);
    bool isExamineCellsInSquare(const n_FrameworkLib::CPosition& position,
            const int32_t& northStart, const int32_t& northEnd,
            const int32_t& eastStart, const int32_t& eastEnd,
                                std::unordered_multimap<std::pair<int32_t, int32_t>, int64_t, PairIdHash >& cellVsNodeIds,
            double& candidateLength_m, int64_t& candidateNodeId);
    bool isExamineCell(const n_FrameworkLib::CPosition& position,
            const int32_t& north, const int32_t& east,
                       std::unordered_multimap<std::pair<int32_t, int32_t>, int64_t, PairIdHash >& cellVsNodeIds,
            double& candidateLength_m, int64_t& candidateNodeId);
    void savePythonPlotCode();
    void findRoadIntersectionsOfCircle(const n_FrameworkLib::CPosition& center, const double& radius_m,
            std::vector<n_FrameworkLib::CPosition>& intersections);

    bool isGetNodesOnSegment(const std::pair<int64_t, int64_t>& segmentNodeIds,
                             const int64_t& startNodeId, const int64_t& endNodeId,
                             const bool& isAddExtraNodeIds,
                             std::vector<int64_t>& nodeIds);
public:

    struct s_PlannerParameters
    {
        double turnRadius_m = {0};
    };

    struct s_EdgeIds
    {
        std::deque<int64_t> m_nodeIds;
        int64_t m_highwayId = -1;
        double m_distance_m = 0;
    };


protected:

    /*! \brief  map from node ID to the planning node index*/
    std::unordered_map<int64_t, int32_t> m_nodeIdVsPlanningIndex;
    /*! \brief  map from planning node index ID to the node*/
    std::shared_ptr<std::unordered_map<int32_t, int64_t> > m_planningIndexVsNodeId;
    /*! \brief  storage for nodes*/
    std::shared_ptr<std::unordered_map<int64_t, std::unique_ptr<n_FrameworkLib::CPosition>>> m_idVsNode;
    /*! \brief  multimap relating way Id to it's Node Id's */
    std::unordered_multimap<int64_t, int64_t> m_wayIdVsNodeId;
    /*! \brief  map from segment begin/end node Ids to node Ids of the contained points */
    std::unordered_multimap<std::pair<int64_t, int64_t>, std::unique_ptr<s_EdgeIds>, PairIdHash > m_nodeIdsVsEdgeNodeIds;
    /*! \brief  map from node Id to segment begin/end node Ids */
    std::unordered_multimap<int64_t, std::pair<int64_t, int64_t>> m_nodeIdVsSegmentBeginEndIds; //
    /*! \brief  multimap from map cell to the node in the cell node, used to
      find closest NodeId to a given North/East point. The cell is a north/east
      pair, defined by dividing the North/East values by a cell length factor */
    std::unordered_multimap<std::pair<int32_t, int32_t>, int64_t, PairIdHash > m_cellVsPlanningNodeIds;
    std::unordered_multimap<std::pair<int32_t, int32_t>, int64_t, PairIdHash > m_cellVsAllNodeIds;
    /*! \brief  used to convert Noth/East to cell Id's */
    int32_t m_PositionToCellFactorNorth_m = 100;
    int32_t m_PositionToCellFactorEast_m = 100;
    int32_t m_northMin_m = 0;
    int32_t m_eastMin_m = 0;

    std::unordered_map<int64_t, std::shared_ptr<afrl::cmasi::EntityConfiguration> > m_entityConfigurations;

    /*! \brief  the name of the openstreetmap file. */
    std::string m_osmFileName;
    /*! \brief  the name of the file for saving map edges. Note: If this string
     * is empty, the edges will not be saved */
    std::string m_mapEdgesFileName;
    /*! \brief  the name of the file for saving the shortest path. Note: If 
     * this string is empty, the shortest path will not be saved */
    std::string m_shortestPathFileName;
    /*! \brief  the name of the file for saving search metrics. Note: If 
     * this string is empty, the search metrics will not be saved */
    std::string m_searchMetricsFileName;
    /*! \brief  the path to the the folder to save files*/
    std::string m_strSavePath;

    std::vector<n_FrameworkLib::CEdge> m_edges; //uses node index
    std::shared_ptr<Graph_t> m_graph;

    int32_t m_numberHighways = 0;
    int32_t m_numberNodes = 0;
    int32_t m_numberPlanningNodes = 0;
    int32_t m_numberPlanningEdges = 0;
    double m_processMapTime_s = 0.0;
    double m_searchTime_s = 0.0;
    double m_processPlanTime_s = 0.0;

private:
    bool isBuildFullPlot(const std::vector<int64_t>& highWayIds);
    uxas::common::utilities::FlatEarth m_flatEarth;


};

// manhattan distance heuristic

class manhattan_distance_heuristic : public boost::astar_heuristic<OsmPlannerService::Graph_t, int64_t>
{
public:

    manhattan_distance_heuristic(std::shared_ptr<std::unordered_map<int64_t, std::unique_ptr<n_FrameworkLib::CPosition> > >& idVsNode,
            std::shared_ptr<std::unordered_map<int32_t, int64_t> >& planningIndexVsNodeId,
            n_FrameworkLib::CPosition& goalPosition)
    : m_idVsNode(idVsNode), m_planningIndexVsNodeId(planningIndexVsNodeId), m_goalPosition(goalPosition) { }

    int64_t operator()(OsmPlannerService::VertexDescriptor_t v)
    {
        int64_t returnDistance((std::numeric_limits<int64_t>::max)());

        auto itNodeId = m_planningIndexVsNodeId->find(v);
        if (itNodeId != m_planningIndexVsNodeId->end())
        {
            auto itPosition = m_idVsNode->find(itNodeId->second);
            if (itPosition != m_idVsNode->end())
            {
                returnDistance = (m_goalPosition.m_north_m - itPosition->second->m_north_m) +
                        (m_goalPosition.m_east_m - itPosition->second->m_east_m);
            }
        }
        return (returnDistance);
    }

private:
    std::shared_ptr<std::unordered_map<int64_t, std::unique_ptr<n_FrameworkLib::CPosition> > > m_idVsNode;
    std::shared_ptr<std::unordered_map<int32_t, int64_t> > m_planningIndexVsNodeId;
    n_FrameworkLib::CPosition m_goalPosition;
};

// euclidean distance heuristic

class euclidean_distance_heuristic : public boost::astar_heuristic<OsmPlannerService::Graph_t, int64_t>
{
public:

    euclidean_distance_heuristic(std::shared_ptr<std::unordered_map<int64_t, std::unique_ptr<n_FrameworkLib::CPosition> > >& idVsNode,
            std::shared_ptr<std::unordered_map<int32_t, int64_t> >& planningIndexVsNodeId,
            n_FrameworkLib::CPosition& goalPosition)
    : m_idVsNode(idVsNode), m_planningIndexVsNodeId(planningIndexVsNodeId), m_goalPosition(goalPosition) { }

    int64_t operator()(OsmPlannerService::VertexDescriptor_t v)
    {
        int64_t returnDistance((std::numeric_limits<int64_t>::max)());

        auto itNodeId = m_planningIndexVsNodeId->find(v);
        if (itNodeId != m_planningIndexVsNodeId->end())
        {
            auto itPosition = m_idVsNode->find(itNodeId->second);
            if (itPosition != m_idVsNode->end())
            {
                returnDistance = static_cast<int64_t> (sqrt(pow(static_cast<double> (m_goalPosition.m_north_m - itPosition->second->m_north_m), 2.0) +
                        pow(static_cast<double> (m_goalPosition.m_east_m - itPosition->second->m_east_m), 2.0)));
            }
        }
        return (returnDistance);
    }

private:
    std::shared_ptr<std::unordered_map<int64_t, std::unique_ptr<n_FrameworkLib::CPosition> > > m_idVsNode;
    std::shared_ptr<std::unordered_map<int32_t, int64_t> > m_planningIndexVsNodeId;
    n_FrameworkLib::CPosition m_goalPosition;
};

struct found_goal
{
}; // exception for termination

// visitor that terminates when we find the goal

class astar_goal_visitor : public boost::default_astar_visitor
{
public:

    astar_goal_visitor(OsmPlannerService::VertexDescriptor_t goal) : m_goal(goal) { }

    void examine_vertex(OsmPlannerService::VertexDescriptor_t u, const OsmPlannerService::Graph_t& g)
    {
        if (u == m_goal)
            throw found_goal();
    }
private:
private:
    OsmPlannerService::VertexDescriptor_t m_goal;

};




}; //namespace service
}; //namespace uxas

#endif /* UXAS_SERVICE_OSM_PLANNER_SERVICE_H */

