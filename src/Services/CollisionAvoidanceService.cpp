// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   CollisionAvoidanceService.cpp
 * Author: Sagar Chaki <chaki@sei.cmu.edu>
 *
 * Created on June 14, 2017, 10:40 AM
 *
 */

//-- DMPLC Version: 0.2
//-- DMPLC Command Line:  dmplc -g -dl 1 --roles uav:Uav:3 --map small --grid-x 10 --grid-y 10 --grid-z 10 -o example-01-2.mission_example-01.cpp example-01.dmpl

/********************************************************************/
//-- begin target (GNU_CPP) specific thunk
/********************************************************************/

#define GNU_WIN
#include <stdlib.h>
#include "UnitConversions.h"
#include "madara/utility/Utility.h"

int my_sleep (int seconds)
{
    madara::utility::sleep (seconds);
    return 0;
}

int roundNum = 0;
int xi,yi;

void print_int(int i)
{
    printf("%i\n", i);
}

void print_line(int _X)
{
    printf("-");
    for(int i = 0;i < _X;++i) printf("--");
    printf("\n");
}

void print_state(int _X,int _Y,int id, int x, int y, int xf, int yf)
{
    if(roundNum == 0) {
        xi = x; yi = y;
    }

    //for(int i = 0;i < 150;++i) printf("\n");
  
    printf("round = %d : id = %d x = %d y = %d xf = %d yf = %d\n", ++roundNum, id, x, y, xf, yf);
    /*
      printf("_X = %d _Y = %d\n",_X,_Y);
      print_line(_X);
      for(int i = 0;i < _Y;++i) {
      printf("|");
      for(int j = 0;j < _X;++j) {
      //printf("i = %d j = %d\n", i, j);
      if(j == xf && i == yf) printf("o|");        
      else if(j == x && i == y) printf("%d|",id);
      else printf(" |");
      }
      printf("\n");
      print_line(_X);
      }
    */
}


/********************************************************************/
//-- end target (GNU_CPP) specific thunk
/********************************************************************/

/********************************************************************/
//-- begin header files
/********************************************************************/

#include <string>
#include <vector>
#include <sstream>
#include <fstream>
#include <exception>
#include <cassert>
#include <cmath>

#include "CollisionAvoidanceService.hpp"
#include "madara/knowledge/KnowledgeBase.h"
#include "madara/knowledge/KnowledgeRecord.h"
#include "madara/knowledge/Functions.h"
#include "madara/transport/PacketScheduler.h"
#include "madara/threads/Threader.h"
#include "madara/filters/GenericFilters.h"

#include "gams/controllers/BaseController.h"
#include "gams/algorithms/BaseAlgorithm.h"
#include "gams/variables/Sensor.h"
#include "gams/platforms/BasePlatform.h"
#include "gams/variables/Self.h"
#include "gams/utility/GPSPosition.h"

#include "dmpl/Reference.hpp"
#include "dmpl/CachedReference.hpp"
#include "dmpl/ArrayReference.hpp"
#include "dmpl/ProactiveStorage.hpp"
#include "dmpl/DefaultLogger.hpp"

/********************************************************************/
//-- end header files
/********************************************************************/

/********************************************************************/
//-- Defining program-specific constants
/********************************************************************/
#define MSG_MARKER "message: "
#define NEXT 1
#define REQUEST 2
#define WAITING 3
#define MOVE 4
#define X 10
#define Y 10
#define Z 10
#define STRING_XML_COLLISION_AVOIDANCE "CollisionAvoidance"
#define MAX_LOCK 10

namespace
{
    //-- minimum and maximum latitide and longitude of the visible
    //-- map area
    const double LAT_MIN = 45.296;
    const double LAT_MAX = 45.35;
    const double LNG_MIN = -121.02;
    const double LNG_MAX = -120.91;
    const double CELL_LAT = (LAT_MAX - LAT_MIN) / (Y-1);
    const double CELL_LNG = (LNG_MAX - LNG_MIN) / (X-1);

    //-- a cell id -- pair of X and Y coordinates
    typedef std::pair<int,int> Cell;
    
    //-- function to convert from a position to cell coordinates
    Cell GpsToCell(double lat, double lng)
    {
        double cellx = (lng - (LNG_MIN - CELL_LNG / 2)) / CELL_LNG;
        int icellx = (int)(floor(cellx));
        double celly = (lat - (LAT_MIN - CELL_LAT / 2)) / CELL_LAT;
        int icelly = (int)(floor(celly));
        return Cell(icellx, icelly);
    }

    //-- return the GPS location of the center of a cell.
    gams::pose::Position CellToGps(int x, int y)
    {
        gams::pose::Position res(uxas::service::GamsService::frame());
        res.lng(LNG_MIN + x * CELL_LNG);
        res.lat(LAT_MIN + y * CELL_LAT);
        return res;
    }

}

// begin dmpl namespace
namespace dmpl
{

    /********************************************************************/
    //-- typedefs
    /********************************************************************/
    typedef   madara::knowledge::KnowledgeRecord::Integer   Integer;

    /********************************************************************/
    //-- namespace shortcuts
    /********************************************************************/
    namespace engine = madara::knowledge;
    namespace threads = madara::threads;
    namespace containers = engine::containers;
    namespace controllers = gams::controllers;
    namespace platforms = gams::platforms;
    namespace variables = gams::variables;

    /********************************************************************/
    //-- for readability so we don't have to use full namespaces
    /********************************************************************/
    using containers::Reference;
    using containers::ArrayReference;
    using containers::CachedReference;
    using containers::StorageManager::Proactive;
    using madara::knowledge::knowledge_cast;
    using madara::knowledge::KnowledgeRecord;
    using madara::knowledge::KnowledgeMap;

    /********************************************************************/
    //-- debug flag
    /********************************************************************/
    bool debug = 0;

    /********************************************************************/
    //-- declare knowledge base
    /********************************************************************/
    engine::KnowledgeBase &knowledge = uxas::service::GamsService::s_knowledgeBase;

    /********************************************************************/
    //-- Needed as a workaround for non-const-correctness in Madara;
    //-- Use carefully
    /********************************************************************/
    inline engine::FunctionArguments &__strip_const(const engine::FunctionArguments &c)
    {
        return const_cast<engine::FunctionArguments &>(c);
    }

    /********************************************************************/
    //-- Needed to construct function arguments
    /********************************************************************/
    inline engine::FunctionArguments &__chain_set(engine::FunctionArguments &c, int i, KnowledgeRecord v)
    {
        c[i] = v;
        return c;
    }

    /********************************************************************/
    //-- default transport variables
    /********************************************************************/
    std::string host ("");
    std::vector<std::string> platform_params;
    std::string platform_name ("debug");
    typedef void (*PlatformInitFn)(const std::vector<std::string> &, engine::KnowledgeBase &, engine::KnowledgeMap &);
    typedef std::map<std::string, PlatformInitFn> PlatformInitFns;
    //PlatformInitFns platform_init_fns;
    const std::string default_multicast ("239.255.0.1:4150");
    madara::transport::QoSTransportSettings settings;
    int write_fd (-1);
    ofstream expect_file;
    std::string node_name ("none");
    std::string role_name ("none");
    struct JobAbortException : public std::exception {};

    /********************************************************************/
    //-- Containers for commonly used global variables
    /********************************************************************/
    Reference<unsigned int> id(knowledge, ".uxas_id");
    Reference<unsigned int>  num_processes(knowledge, ".num_processes");
    engine::KnowledgeUpdateSettings private_update (true);

    //-- used to synchronize and make sure that all nodes are up
    ArrayReference<unsigned int, 2> startSync(knowledge, "startSync");
    Reference<unsigned int> syncPhase(knowledge, ".syncPhase");

    KnowledgeRecord
    sync_inputs (engine::FunctionArguments & args, engine::Variables & vars)
    {
        std::string syncStr("REMODIFY_INPUT_GLOBALS () ; startSync.{.uxas_id} = .syncPhase");
        knowledge.evaluate (syncStr);
        return Integer(0);
    }

    /********************************************************************/
    //-- barrier variables
    /********************************************************************/
    ArrayReference<unsigned int, 2> mbarrier_COLLISION_AVOIDANCE(knowledge, "mbarrier_COLLISION_AVOIDANCE");

    /********************************************************************/
    //-- map from synchronous threads to synchronous partner node ids
    /********************************************************************/
    std::map< std::string,std::map< size_t,std::set<size_t> > > syncPartnerIds;

    /********************************************************************/
    //-- function from node ids and role names to node ids
    /********************************************************************/
    size_t role2Id(size_t nodeId, const std::string &roleName);

    /********************************************************************/
    //-- number of participating processes
    /********************************************************************/
    unsigned int processes (2);

    /********************************************************************/
    //-- Begin defining variables for node uav
    /********************************************************************/

    // begin node_uav namespace
    namespace node_uav
    {        
        /********************************************************************/
        //-- Defining global variables at node scope
        /********************************************************************/
        ArrayReference<int, 2, MAX_LOCK> lock(knowledge, "lock");
        ArrayReference<_Bool, 2> missionOver(knowledge, "missionOver");
        _Bool var_init_missionOver (0);

        /********************************************************************/
        //-- Defining group variables at node scope
        /********************************************************************/

        /********************************************************************/
        //-- Defining local variables at node scope
        /********************************************************************/
        Reference<short> state(knowledge, ".state");
        short var_init_state (0);
        Reference<short> x(knowledge, ".x");
        short var_init_x (0);
        Reference<short> xf(knowledge, ".xf");
        short var_init_xf (0);
        Reference<short> xp(knowledge, ".xp");
        short var_init_xp (0);
        Reference<short> y(knowledge, ".y");
        short var_init_y (0);
        Reference<short> yf(knowledge, ".yf");
        short var_init_yf (0);
        Reference<short> yp(knowledge, ".yp");
        short var_init_yp (0);

        //-- initial latitude and longitude
        double init_lat = 0, init_lng = 0;
        
        //-- pointer to list of future waypoints
        std::list<std::shared_ptr<afrl::cmasi::Waypoint>> *wpPtr = NULL;
    
        //-- the current wapoint we are at
        std::shared_ptr<afrl::cmasi::Waypoint> currWP;

        //-- the next waypoint we are moving toward
        std::shared_ptr<afrl::cmasi::Waypoint> nextWP;

        //-- the next position we are moving toward. this is updated along with xp and yp.
        gams::pose::Position nextPos(uxas::service::GamsService::frame());
    
        //-- lock to implement mutex for wpPtr and nextWP
        std::mutex wpLock;

        //-- the loitering radius of the vehicle in meters
        double loiterRadius = 0;
        
        //-- set of cells to lock during next movement
        std::set<Cell> cellsToLock;
        
        /********************************************************************/
        //-- functions to manipulate locks
        /********************************************************************/

        void setOnlyLock(int _x, int _y)
        {
            lock[id][0] = _x * Y + _y;
            for(int i = 1;i < MAX_LOCK;++i)
            {
                lock[id][i] = -1;
            }
        }
        
        /********************************************************************/
        //-- Begin defining variables for role Uav
        /********************************************************************/

        // begin node_uav_role_Uav namespace
        namespace node_uav_role_Uav
        {

            /********************************************************************/
            //-- Defining global variables at role scope
            /********************************************************************/

            /********************************************************************/
            //-- Defining group variables at role scope
            /********************************************************************/

            /********************************************************************/
            //-- Defining local variables at role scope
            /********************************************************************/

            /********************************************************************/
            //-- Defining local variables at scope of thread COLLISION_AVOIDANCE
            //-- Used to implement Read-Execute-Write semantics
            /********************************************************************/
            CachedReference<short> thread0_state(knowledge, ".state");
            CachedReference<short> thread0_x(knowledge, ".x");
            CachedReference<short> thread0_xf(knowledge, ".xf");
            CachedReference<short> thread0_xp(knowledge, ".xp");
            CachedReference<short> thread0_y(knowledge, ".y");
            CachedReference<short> thread0_yf(knowledge, ".yf");
            CachedReference<short> thread0_yp(knowledge, ".yp");

            /********************************************************************/
            //-- Defining global variables at scope of thread COLLISION_AVOIDANCE
            //-- Used to implement Read-Execute-Write semantics
            /********************************************************************/
            ArrayReference<Proactive<int, CachedReference>, 2, MAX_LOCK> thread0_lock(knowledge, "lock");
            ArrayReference<Proactive<_Bool, CachedReference>, 2> thread0_missionOver(knowledge, "missionOver");

            /********************************************************************/
            //-- functions to manipulate locks
            /********************************************************************/

            //-- return true if cell (x,y) is locked by node _id
            bool isLockedThread(int _id, int _x, int _y)
            {
                for(int i = 0;i < MAX_LOCK;++i)
                {
                    int lockVal = thread0_lock[_id][i];
                    if(lockVal < 0) continue;
                    if((lockVal % Y) != _y) continue;
                    if((lockVal / Y) != _x) continue;
                    return true;
                }
                
                return false;
            }

            //-- return true if any cell in cells is locked by node
            //-- _id
            bool isLockedThread(int _id, const std::set<Cell> &cells)
            {
                for(const auto &cell : cells)
                {
                    if(isLockedThread(_id, cell.first, cell.second))
                    {
                        return true;
                    }
                }
                return false;
            }

            //-- lock cell (x,y)
            void setLockThread(int _x, int _y)
            {
                if(isLockedThread(id, _x, _y)) return;
                
                for(int i = 0;i < MAX_LOCK;++i)
                {
                    if(thread0_lock[id][i] < 0)
                    {
                        thread0_lock[id][i] = _x * Y + _y;
                        return;
                    }
                }
                assert(0);
            }

            //-- lock all cells in cells
            void setLockThread(const std::set<Cell> &cells)
            {
                for(const auto &cell : cells)
                {
                    setLockThread(cell.first, cell.second);
                }
            }

            //-- unlock cell (x,y)
            void unsetLockThread(int _x, int _y)
            {
                for(int i = 0;i < MAX_LOCK;++i)
                {
                    int lockVal = thread0_lock[id][i];
                    if(lockVal < 0) continue;
                    if((lockVal % Y) != _y) continue;
                    if((lockVal / Y) != _x) continue;
                    thread0_lock[id][i] = -1;
                }
            }

            //-- unlock all cells in cells
            void unsetLockThread(const std::set<Cell> &cells)
            {
                for(const auto &cell : cells)
                {
                    unsetLockThread(cell.first, cell.second);
                }
            }
            
            /********************************************************************/
            //-- Defining group variables at scope of thread COLLISION_AVOIDANCE
            //-- Used to implement Read-Execute-Write semantics
            /********************************************************************/

        } // end node_uav_role_Uav namespace

        /********************************************************************/
        //-- End defining variables for role Uav
        /********************************************************************/

    } // end node_uav namespace

    /********************************************************************/
    //-- End defining variables for node uav
    /********************************************************************/

    /********************************************************************/
    //-- helper tokenizer method to handle command line arguments
    /********************************************************************/
    template < class ContainerT >
    void tokenize(const std::string& str, ContainerT& tokens,
                  const std::string& delimiters = " ", bool trimEmpty = false)
    {
        std::string::size_type pos, lastPos = 0;

        typedef typename ContainerT::value_type value_type;
        typedef typename ContainerT::size_type size_type;

        while(true)
        {
            pos = str.find_first_of(delimiters, lastPos);
            if(pos == std::string::npos)
            {
                pos = str.length();

                if(pos != lastPos || !trimEmpty)
                    tokens.push_back(value_type(str.data()+lastPos,
                                                (size_type)pos-lastPos ));

                break;
            }
            else
            {
                if(pos != lastPos || !trimEmpty)
                    tokens.push_back(value_type(str.data()+lastPos,
                                                (size_type)pos-lastPos ));
            }

            lastPos = pos + 1;
        }
    }

    /********************************************************************/
    //-- helper function to check validity of supplied arguments
    /********************************************************************/
    void check_argument_sanity()
    {
        if(node_name == "uav" && role_name == "Uav") return;
        throw std::runtime_error("ERROR : illegal node and role combination : ("
                                 + node_name + " , " + role_name + ")");
    }

    /********************************************************************/
    //-- Forward declaring global functions
    /********************************************************************/

    /********************************************************************/
    //-- Forward declaring node and role functions
    /********************************************************************/
    // begin node_uav namespace
    namespace node_uav
    {

        /********************************************************************/
        //-- Declaring functions for role Uav
        /********************************************************************/

        // begin node_uav_role_Uav namespace
        namespace node_uav_role_Uav
        {
            KnowledgeRecord
            thread0_PULL (engine::FunctionArguments & args, engine::Variables & vars);
            KnowledgeRecord
            thread0_PUSH (engine::FunctionArguments & args, engine::Variables & vars);
            KnowledgeRecord
            thread0 (engine::FunctionArguments & args, engine::Variables & vars);
            KnowledgeRecord
            thread0_COLLISION_AVOIDANCE (engine::FunctionArguments & args, engine::Variables & vars);
            void thread0_NEXT_WP ();
            void thread0_NEXT_XY_Rec (double x1, double y1, double x2, double y2);
            KnowledgeRecord
            thread0_NEXT_XY (engine::FunctionArguments & args, engine::Variables & vars);
        } // end node_uav_role_Uav namespace

    } // end node_uav namespace

} // end dmpl namespace


/********************************************************************/
//-- GAMS variables and functions
/********************************************************************/

// begin dmpl namespace
namespace dmpl
{

    /********************************************************************/
    //-- Defining global functions
    /********************************************************************/


    /********************************************************************/
    //-- Begin node uav
    /********************************************************************/

    // begin node_uav namespace
    namespace node_uav
    {

        /********************************************************************/
        //-- Defining functions for role Uav
        /********************************************************************/

        // begin node_uav_role_Uav namespace
        namespace node_uav_role_Uav
        {

            /***********************************/
            //given a point, compute the set of cells that the node
            //can traverse while loitering around that point.
            /***********************************/
            std::set<Cell> cellsLoitered(double x, double y)
            {
                uxas::common::utilities::CUnitConversions flatEarth;       
                double north, east;
                flatEarth.ConvertLatLong_degToNorthEast_m(y, x, north, east);
                double minLat, maxLat, minLng, maxLng, lat, lng;
                flatEarth.ConvertNorthEast_mToLatLong_deg(north - loiterRadius, east, minLat, lng);
                flatEarth.ConvertNorthEast_mToLatLong_deg(north + loiterRadius, east, maxLat, lng);
                flatEarth.ConvertNorthEast_mToLatLong_deg(north, east - loiterRadius, lat, minLng);
                flatEarth.ConvertNorthEast_mToLatLong_deg(north, east + loiterRadius, lat, maxLng);

                auto minCell = GpsToCell(minLat, minLng);
                auto maxCell = GpsToCell(maxLat, maxLng);

                std::set<Cell> res;

                /*
                for(int i = minCell.first;i <= maxCell.first;++i)
                {
                    for(int j = minCell.second;j <= maxCell.second;++j)
                    {
                        res.insert(Cell(i,j));
                    }
                }
                */
                
                return res;
            }

            bool adjacentCells(const Cell &cell1, const Cell &cell2)
            {
                if((cell1.first == cell2.first) &&
                   ((cell1.second == cell2.second + 1) || (cell1.second == cell2.second - 1))) return true;

                if((cell1.second == cell2.second) &&
                   ((cell1.first == cell2.first + 1) || (cell1.first == cell2.first - 1))) return true;

                return false;
            }

            bool diagonalCells(const Cell &cell1, const Cell &cell2)
            {
                return (((cell1.first == cell2.first + 1) || (cell1.first == cell2.first - 1)) &&
                        ((cell1.second == cell2.second + 1) || (cell1.second == cell2.second - 1)));
            }
            
            std::set<Cell> cellsTraversedRec(double x1, double y1, double x2, double y2)
            {
                //-- compute the cells that the two points are in
                auto cell1 = GpsToCell(y1, x1);
                auto cell2 = GpsToCell(y2, x2);

                if(cell1 == cell2)
                {
                    std::set<Cell> res;
                    res.insert(cell1);
                    return res;
                }

                if(adjacentCells(cell1, cell2))
                {
                    std::set<Cell> res;
                    res.insert(cell1);
                    res.insert(cell2);
                    return res;
                }

                if(diagonalCells(cell1, cell2))
                {
                    std::set<Cell> res;
                    res.insert(cell1);
                    res.insert(cell2);
                    res.insert(Cell(cell1.first, cell2.second));
                    res.insert(Cell(cell2.first, cell1.second));
                    return res;
                }

                double xmid = (x1 + x2) / 2;
                double ymid = (y1 + y2) / 2;

                std::set<Cell> res1 = cellsTraversedRec(x1, y1, xmid, ymid);
                std::set<Cell> res2 = cellsTraversedRec(xmid, ymid, x2, y2);

                res1.insert(res2.begin(), res2.end());
                return res1;
            }
            
            /***********************************/
            //-- given two points P1 and P2, compute the sequence of
            //-- cells that must be traversed if traveling in a
            //-- straight line from P1 to P2. essentially we compute
            //-- the set of cells in the rectangle whose diagonals are
            //-- defined by the two points.
            /***********************************/
            std::set<Cell> cellsTraversed(double x1, double y1, double x2, double y2)
            {
                std::set<Cell> res = cellsTraversedRec(x1, y1, x2, y2);

                //-- add the set of cells that may be traversed when
                //-- loitering at (x2, y2).
                for(const auto &c : cellsLoitered(x2, y2))
                {
                    res.insert(c);
                }

                return res;
            }

            /********************************************************************/
            //-- Remodify input global shared variables to force MADARA retransmit
            /********************************************************************/
            KnowledgeRecord
            REMODIFY_INPUT_GLOBALS (engine::FunctionArguments & args,
                                    engine::Variables & vars)
            {
                // Remodifying role-specific global and group variables
                return Integer (0);
            }

            /********************************************************************/
            //-- Remodify barries variables to force MADARA retransmit
            /********************************************************************/
            KnowledgeRecord
            REMODIFY_BARRIERS_COLLISION_AVOIDANCE (engine::FunctionArguments &,
                                                   engine::Variables & vars)
            {
                mark_modified(mbarrier_COLLISION_AVOIDANCE[id]);
                return Integer (0);
            }

            /********************************************************************/
            //-- Remodify global shared variables to force MADARA retransmit
            /********************************************************************/
            KnowledgeRecord
            REMODIFY_GLOBALS_COLLISION_AVOIDANCE (engine::FunctionArguments & args,
                                                  engine::Variables & vars)
            {
                // Remodifying common global variables
                REMODIFY_BARRIERS_COLLISION_AVOIDANCE (args, vars);
                // Remodifying thread-specific global variables
                mark_modified(lock[id]);
                mark_modified(missionOver[id]);
                // Remodifying thread-specific group variables
                return Integer (0);
            }

            KnowledgeRecord
            thread0_PULL (engine::FunctionArguments & args, engine::Variables & vars)
            {
                //-- Pull all referenced locals/globals
                {
                    madara::knowledge::ContextGuard guard(knowledge);
                    pull(thread0_state);
                    pull(thread0_x);
                    pull(thread0_xf);
                    pull(thread0_xp);
                    pull(thread0_y);
                    pull(thread0_yf);
                    pull(thread0_yp);
                    pull(thread0_lock);
                    pull(thread0_missionOver);
                }
                return Integer(0);
            }

            KnowledgeRecord
            thread0_PUSH (engine::FunctionArguments & args, engine::Variables & vars)
            {
                //-- Push all referenced locals/globals
                {
                    madara::knowledge::ContextGuard guard(knowledge);
                    push(thread0_state);
                    push(thread0_x);
                    push(thread0_xf);
                    push(thread0_xp);
                    push(thread0_y);
                    push(thread0_yf);
                    push(thread0_yp);
                    push(thread0_lock[id]);
                    push(thread0_missionOver[id]);
                }
                return Integer(0);
            }

            KnowledgeRecord
            thread0 (engine::FunctionArguments & args, engine::Variables & vars)
            {
                //-- call thread function
                try {
                    thread0_COLLISION_AVOIDANCE(args, vars);
                } catch (JobAbortException &ex) {}

                return Integer(0);
            }

            KnowledgeRecord
            thread0_COLLISION_AVOIDANCE (engine::FunctionArguments & args, engine::Variables & vars)
            {

                //-- Declare local (parameter and temporary) variables
                //print_state(10,10,id, thread0_x, thread0_y, thread0_xf, thread0_yf);

                //-- Begin function body
                {
                    (void) (std::cerr  << MSG_MARKER << "id = " << id << " X = " << X << " Y = " << Y << " x = " << thread0_x << " y = " << thread0_y << " state = " << thread0_state << "\n");
                }
                if ((thread0_state == NEXT))
                {
                    //-- check if we need to update nextWP
                    if(nextWP == NULL || (nextPos.lat() == nextWP->getLatitude() && nextPos.lng() == nextWP->getLongitude()))
                    {
                        //-- check if there are no more waypoints
                        {
                            std::lock_guard<std::mutex> lockGuard(node_uav::wpLock);
                            if(wpPtr->empty())
                            {
                                return Integer(0);
                            }
                        }
                        //-- update next waypoint
                        thread0_NEXT_WP();
                    }

                    //-- if the next waypoint is in the same cell as we are in, then move directly to there
                    if(thread0_x == thread0_xf && thread0_y == thread0_yf)
                    {
                        nextPos.lat(nextWP->getLatitude());
                        nextPos.lng(nextWP->getLongitude());
                        thread0_state = MOVE;
                    }
                    else        
                    {
                        (void) (thread0_NEXT_XY (
                                    __strip_const(engine::FunctionArguments(0))
                                    , vars));
        
                        //-- if the next waypoint is in the same cell as we are in, then move directly to there
                        if(thread0_x == thread0_xp && thread0_y == thread0_yp)
                        {
                            thread0_state = MOVE;
                        }
                        else
                        {
                            thread0_state = REQUEST;
                        }
                    }
                }
                else
                {
                    if ((thread0_state == REQUEST))
                    {
                        if (id == 1 && isLockedThread(0, cellsToLock))
                        {
                            return Integer(0);
                        }
                        setLockThread(cellsToLock);
                        thread0_state = WAITING;
                    }
                    else
                    {
                        if ((thread0_state == WAITING))
                        {
                            if (id == 0 && isLockedThread(1, cellsToLock))
                            {
                                return Integer(0);
                            }
                            thread0_state = MOVE;
                        }
                        else
                        {
                            if ((thread0_state == MOVE))
                            {
                                nextPos.alt(nextWP->getAltitude());
                                std::cerr << "GAMS::move " << nextPos << '\n';
                                if(uxas::service::GamsService::move (nextPos, nextWP) != gams::platforms::PLATFORM_ARRIVED)
                                {
                                    return Integer(0);
                                }
                                unsetLockThread(thread0_x, thread0_y);
                                unsetLockThread(cellsToLock);
                                currWP = nextWP;
                                thread0_x = thread0_xp;
                                thread0_y = thread0_yp;
                                setLockThread(thread0_x, thread0_y);
                                setLockThread(cellsLoitered(currWP->getLongitude(),currWP->getLatitude()));
                                thread0_state = NEXT;
                                std::cerr << "current waypoint cell = (" << thread0_x << ',' << thread0_y << ") ...\n";
                            }
                        }
                    }
                }

                //-- Insert return statement, in case user program did not
                return Integer(0);
            }

            /***********************************/
            //-- update xf and yf
            /***********************************/
            void thread0_NEXT_WP ()
            {
                //-- update list of waypoints. make sure you get the lock.
                {
                    std::lock_guard<std::mutex> lockGuard(wpLock);
                    nextWP = wpPtr->front();
                    wpPtr->pop_front();
                }
      
                auto nextCell = GpsToCell(nextWP->getLatitude(), nextWP->getLongitude());
                thread0_xf = nextCell.first;
                thread0_yf = nextCell.second;

                std::cerr << "next waypoint Number = " << nextWP->getNumber() << '\n';
                std::cerr << "next waypoint GPS = (" << nextWP->getLatitude()
                          << ',' << nextWP->getLongitude() << ") ...\n";
                std::cerr << "next waypoint cell = (" << thread0_xf << ',' << thread0_yf << ") ...\n";
            }
            
            /***********************************/
            //-- update xp and yp recursively
            /***********************************/
            void thread0_NEXT_XY_Rec(double x1, double y1, double x2, double y2)
            {
                //-- compute the cells that the two points are in
                auto cell1 = GpsToCell(y1, x1);
                auto cell2 = GpsToCell(y2, x2);

                if(cell1 == cell2)
                {
                    assert(0 && "ERROR: cannot be in nextWP at this stage!!");                    
                }

                if(adjacentCells(cell1, cell2))
                {
                    thread0_xp = cell2.first;
                    thread0_yp = cell2.second;
                    cellsToLock.clear();
                    cellsToLock.insert(cell2);
                    nextPos.lat(y2);
                    nextPos.lng(x2);
                    return;
                }

                if(diagonalCells(cell1, cell2))
                {
                    thread0_xp = cell2.first;
                    thread0_yp = cell2.second;
                    cellsToLock.clear();
                    cellsToLock.insert(cell2);
                    cellsToLock.insert(Cell(cell1.first, cell2.second));
                    cellsToLock.insert(Cell(cell2.first, cell1.second));
                    nextPos.lat(y2);
                    nextPos.lng(x2);
                    return;
                }

                double xmid = (x1 + x2) / 2;
                double ymid = (y1 + y2) / 2;
                thread0_NEXT_XY_Rec(x1, y1, xmid, ymid);
            }
            
            /***********************************/
            //-- update xp and yp
            /***********************************/
            KnowledgeRecord
            thread0_NEXT_XY (engine::FunctionArguments & args, engine::Variables & vars)
            {
                std::cerr << "current cell = (" << thread0_x << ',' << thread0_y << ") ...\n";

#if 1
                thread0_NEXT_XY_Rec(currWP->getLongitude(),currWP->getLatitude(),
                                    nextWP->getLongitude(),nextWP->getLatitude());
                /*
                //-- Begin function body
                thread0_xp = thread0_xf;
                thread0_yp = thread0_yf;

                //-- update cells to lock
                cellsToLock.clear();
                cellsToLock = cellsTraversed(currWP->getLongitude(),currWP->getLatitude(),
                                             nextWP->getLongitude(),nextWP->getLatitude());
                */
#else
                thread0_xp = thread0_x;
                thread0_yp = thread0_y;
                if ((thread0_x < thread0_xf))
                {
                    thread0_xp = (thread0_xp + Integer (1));
                }
                else
                {
                    if ((thread0_x > thread0_xf))
                    {
                        thread0_xp = (thread0_xp - Integer (1));
                    }
                    else
                    {
                        if ((thread0_y < thread0_yf))
                        {
                            thread0_yp = (thread0_yp + Integer (1));
                        }
                        else
                        {
                            thread0_yp = (thread0_yp - Integer (1));
                        }
                    }
                }
                
                cellsToLock.clear();
                cellsToLock.insert(Cell(thread0_xp, thread0_yp));
#endif
                
                std::cerr << "next cell = (" << thread0_xp << ',' << thread0_yp << ") ...\n";

                /*
                //-- if the next cell contains the next waypoint, then move to the
                //-- waypoint.
                if(thread0_xp == thread0_xf && thread0_yp == thread0_yf)
                {
                    nextPos.lat(nextWP->getLatitude());
                    nextPos.lng(nextWP->getLongitude());
                }
                //-- otherwise move to the center of the next cell
                else
                {
                    nextPos = CellToGps(thread0_xp, thread0_yp);
                }
                */
  
                //-- Insert return statement, in case user program did not
                return Integer(0);
            }

            /********************************************************************/
            //-- Begin constructors for role Uav
            /********************************************************************/
            void initialize_lock ()
            {
                engine::Variables vars;
                setOnlyLock(x, y);
            }
            void initialize_missionOver ()
            {
                engine::Variables vars;
                missionOver[id] = Integer (0);
            }
            void initialize_state ()
            {
                engine::Variables vars;
                state = NEXT;
            }
            int check_init_x ()
            {
                engine::Variables vars;
                x = var_init_x;
                return (Integer(((Integer (0) <= x) && (x < X))));
            }
            int check_init_xf ()
            {
                engine::Variables vars;
                xf = var_init_xf;
                return (Integer(((Integer (0) <= xf) && (xf < X))));
            }
            void initialize_xp ()
            {
                engine::Variables vars;
                xp = x;
            }
            int check_init_y ()
            {
                engine::Variables vars;
                y = var_init_y;
                return (Integer(((Integer (0) <= y) && (y < Y))));
            }
            int check_init_yf ()
            {
                engine::Variables vars;
                yf = var_init_yf;
                return (Integer(((Integer (0) <= yf) && (yf < Y))));
            }
            void initialize_yp ()
            {
                engine::Variables vars;
                yp = y;
            }
            void constructor ()
            {
                if(!check_init_x ()) throw std::runtime_error("ERROR: illegal initial value of variable x");
                if(!check_init_y ()) throw std::runtime_error("ERROR: illegal initial value of variable y");
                initialize_lock ();
                initialize_missionOver ();
                initialize_state ();
                if(!check_init_xf ()) throw std::runtime_error("ERROR: illegal initial value of variable xf");
                initialize_xp ();
                if(!check_init_yf ()) throw std::runtime_error("ERROR: illegal initial value of variable yf");
                initialize_yp ();
                nextPos = gams::pose::Position(uxas::service::GamsService::frame());
                nextPos.lng(init_lng);
                nextPos.lat(init_lat);
            }

        } // end node_uav_role_Uav namespace

    } // end node_uav namespace


    /********************************************************************/
    //-- End node uav
    /********************************************************************/


    /********************************************************************/
    //-- Class that encapsulates a periodic thread
    /********************************************************************/

    class Algo : public gams::algorithms::BaseAlgorithm, protected threads::BaseThread
    {
    public:
        Algo (
            unsigned period,
            const std::string &exec_func,
            madara::knowledge::KnowledgeBase * knowledge = 0,
            const std::string &platform_name = "",
            const engine::KnowledgeMap *platform_args = NULL,
            variables::Sensors * sensors = 0,
            variables::Self * self = 0);
        ~Algo (void);
        virtual int analyze (void);
        virtual int plan (void);
        virtual int execute (void);
        virtual void init (engine::KnowledgeBase & context);
        virtual void init_platform ();
        virtual void run (void);
        virtual void cleanup (void);
        virtual void start (threads::Threader &threader);
    protected:
        unsigned _period; //-- period in us
        controllers::BaseController loop;
        engine::KnowledgeBase *knowledge_;
        std::string _exec_func, _platform_name;
        const engine::KnowledgeMap *_platform_args;
    };

    /********************************************************************/
    //-- Class that encapsulates a synchronous periodic thread
    /********************************************************************/

    class SyncAlgo : public Algo
    {
    public:
        SyncAlgo (
            unsigned period,
            const std::string &exec_func,
            const std::string &thread_name,
            madara::knowledge::KnowledgeBase * knowledge = 0,
            const std::string &platform_name = "",
            const engine::KnowledgeMap *platform_args = NULL,
            variables::Sensors * sensors = 0,
            variables::Self * self = 0);
        ~SyncAlgo (void);
        virtual int analyze (void);
        virtual int plan (void);
        virtual int execute (void);
        virtual void init (engine::KnowledgeBase & context);
        virtual void run (void);
        virtual void cleanup (void);
    protected:
        int phase;
        std::string mbarrier;
        madara::knowledge::WaitSettings wait_settings;
        engine::CompiledExpression round_logic;
        std::stringstream barrier_data_string;
        engine::CompiledExpression barrier_data_logic;
    };


    /********************************************************************/
    //-- Begin Algo class methods
    /********************************************************************/

    Algo::Algo (
        unsigned period,
        const std::string &exec_func,
        madara::knowledge::KnowledgeBase * knowledge,
        const std::string &platform_name,
        const engine::KnowledgeMap *platform_args,
        variables::Sensors * sensors,
        variables::Self * self) : loop(*knowledge),
                                  _platform_name(platform_name), _platform_args(platform_args),
                                  BaseAlgorithm (knowledge, 0, sensors, self), knowledge_(knowledge),
                                  _period(period), _exec_func(exec_func)
    {
    }

    Algo::~Algo (void)
    {
    }

    int Algo::analyze (void)
    {
        return 0;
    }

    int Algo::plan (void)
    {
        return 0;
    }

    void Algo::init (engine::KnowledgeBase & context)
    {
        loop.init_vars (settings.id, processes);
        if(_platform_name != "") init_platform ();
        loop.init_algorithm (this);
    }

    void Algo::run (void)
    {
        loop.run_once(); 
    }

    void Algo::init_platform ()
    {
        loop.init_platform (_platform_name, *_platform_args);
        //platform = loop.get_platform();
    }

    void Algo::cleanup (void)
    {
    }

    void Algo::start (threads::Threader &threader)
    {
        std::cout << "Starting thread: " << _exec_func << " at period " << _period << " us" << std::endl;
        double hertz = 1000000.0 / _period;
        threader.run(hertz, _exec_func, this);
    }

    int Algo::execute (void)
    {
        if (dmpl::debug)
            std::cout << "Executing thread: " << _exec_func << " at period " << _period << " us" << std::endl;
        knowledge_->evaluate (_exec_func + "_PULL ()");
        knowledge_->evaluate (_exec_func + "()");
        knowledge_->evaluate (_exec_func + "_PUSH ()");
        return 0;
    }

    /********************************************************************/
    //-- End Algo class methods
    /********************************************************************/

    /********************************************************************/
    //-- Begin SyncAlgo class methods
    /********************************************************************/

    SyncAlgo::SyncAlgo (
        unsigned period,
        const std::string &exec_func,
        const std::string &thread_name,
        madara::knowledge::KnowledgeBase * knowledge,
        const std::string &platform_name,
        const engine::KnowledgeMap *platform_args,
        variables::Sensors * sensors,
        variables::Self * self) : phase(0), mbarrier("mbarrier_" + thread_name),
                                  Algo (period, exec_func, knowledge, platform_name, platform_args, sensors, self)
    {
        wait_settings.max_wait_time = 0;
        wait_settings.poll_frequency = .1;

        round_logic = knowledge_->compile (
            knowledge_->expand_statement (_exec_func + " (); ++" + mbarrier + ".{.uxas_id}"));
    }

    SyncAlgo::~SyncAlgo (void)
    {
    }

    void SyncAlgo::init (engine::KnowledgeBase & context)
    {
        bool started = false;

        barrier_data_string << _exec_func << "_REMODIFY_GLOBALS () ;> ";
        // create barrier check for partner ids
        for (size_t i : syncPartnerIds[_exec_func][settings.id])
        {
            if (started)
            {
                barrier_data_string << " && ";
            }

            barrier_data_string << "" + mbarrier + ".";
            barrier_data_string << i;
            barrier_data_string << " >= " + mbarrier + ".";
            barrier_data_string << settings.id;
            if (!started)
                started = true;
        }

        // take care of the case when there are no partner ids
        if (syncPartnerIds[_exec_func][settings.id].empty()) {
            barrier_data_string << "1";
        }

        // Compile frequently used expressions
        barrier_data_logic = knowledge_->compile (barrier_data_string.str ());
        Algo::init(context);
    }

    void SyncAlgo::run (void)
    {
        {
            // Pre-round barrier increment
            if(phase == 0)
            {
                wait_settings.delay_sending_modifieds = true; 
                knowledge_->evaluate ("++" + mbarrier + ".{.uxas_id}", wait_settings); 
                phase++;
            }
            if(phase == 1)
            {
                // remodify our globals and send all updates 
                wait_settings.send_list.clear (); 
                wait_settings.delay_sending_modifieds = false; 
                // first barrier for new data from previous round 
                if(knowledge_->evaluate (barrier_data_logic, wait_settings).to_integer()) 
                    phase++;
            }
            if(phase == 2)
            {
                // Execute main user logic 
                wait_settings.delay_sending_modifieds = true; 
                knowledge_->evaluate (_exec_func + "_PULL ()", wait_settings); 
                Algo::run(); 
                phase++;
            }
            if(phase == 3)
            {
                // second barrier for waiting on others to finish round 
                // Increment barrier and only send barrier update 
                wait_settings.send_list.clear (); 
                wait_settings.delay_sending_modifieds = false; 
                if(knowledge_->evaluate (barrier_data_logic, wait_settings).to_integer()) {
                    wait_settings.delay_sending_modifieds = true; 
                    knowledge_->evaluate (_exec_func + "_PUSH ()", wait_settings); 
                    phase = 0;
                }
            }
        }
    }

    void SyncAlgo::cleanup (void)
    {
    }

    int SyncAlgo::analyze (void)
    {
        return 0;
    }

    int SyncAlgo::plan (void)
    {
        return 0;
    }

    int SyncAlgo::execute (void)
    {
        if (dmpl::debug)
            std::cout << "Executing thread: " << _exec_func << " at period " << _period << " us" << std::endl;
        knowledge_->evaluate (round_logic, wait_settings);
        return 0;
    }

    /********************************************************************/
    //-- End SyncAlgo class methods
    /********************************************************************/
    size_t role2Id(size_t nodeId, const std::string &roleName)
    {
        throw std::runtime_error("ERROR: role2Id called with illegal arguments " + std::to_string(nodeId) + " and " + roleName + "!!");
    }

} // end dmpl namespace

using namespace dmpl;


/********************************************************************/
//-- Helper function to convert objects to strings
/********************************************************************/

template<class T> std::string to_string(const T &in)
{
    std::stringstream ss;
    ss << in;
    return ss.str();
}

/********************************************************************/
//-- the main service class
/********************************************************************/
namespace uxas
{
    namespace service
    {
      
        CollisionAvoidanceService::ServiceBase::CreationRegistrar<CollisionAvoidanceService>
        CollisionAvoidanceService::s_registrar(CollisionAvoidanceService::s_registryServiceTypeNames());

        CollisionAvoidanceService::CollisionAvoidanceService()
            : ServiceBase(CollisionAvoidanceService::s_typeName(),
                          CollisionAvoidanceService::s_directoryName()),
              m_checkpointPrefix ("checkpoints/checkpoint"), m_threader (m_knowledgeBase) {
        };

        CollisionAvoidanceService::~CollisionAvoidanceService() { };

        /********************************************************************/
        //-- handle arguments from the command line
        /********************************************************************/
        void CollisionAvoidanceService::read_arguments (const pugi::xml_node& serviceXmlNode)
        {
            // load settings from the XML file
            for (pugi::xml_node currentXmlNode = serviceXmlNode.first_child();
                 currentXmlNode; currentXmlNode = currentXmlNode.next_sibling())
            {
                // if we need to load initial knowledge
                if (std::string("DART") == currentXmlNode.name())
                {
                    if (!currentXmlNode.attribute("id").empty())
                    {
                        settings.id = currentXmlNode.attribute("id").as_int();
                    }
                    if (!currentXmlNode.attribute("node_name").empty())
                    {
                        node_name = currentXmlNode.attribute("node_name").as_string();
                    }
                    if (!currentXmlNode.attribute("role_name").empty())
                    {
                        role_name = currentXmlNode.attribute("role_name").as_string();
                    }
                    if (!currentXmlNode.attribute("init_lat").empty() &&
                        !currentXmlNode.attribute("init_lng").empty())
                    {
                        node_uav::init_lat = currentXmlNode.attribute("init_lat").as_double();
                        node_uav::init_lng = currentXmlNode.attribute("init_lng").as_double();
                        auto init_cell = GpsToCell(node_uav::init_lat, node_uav::init_lng);
                        std::cerr << "initial cell = " << init_cell.first << "," << init_cell.second << '\n';
                        node_uav::var_init_x = init_cell.first;
                        node_uav::var_init_xf = init_cell.first;
                        node_uav::var_init_y = init_cell.second;
                        node_uav::var_init_yf = init_cell.second;
                        node_uav::currWP = std::shared_ptr<afrl::cmasi::Waypoint>(new afrl::cmasi::Waypoint ());
                        node_uav::currWP->setLatitude(node_uav::init_lat);
                        node_uav::currWP->setLongitude(node_uav::init_lng);
                    }
                    if (!currentXmlNode.attribute("DefaultLoiterRadius_m").empty())
                    {
                        node_uav::loiterRadius = currentXmlNode.attribute("DefaultLoiterRadius_m").as_double();
                    }
                }
                // read a waypoint
                if (std::string("Waypoint") == currentXmlNode.name())
                {
                    std::shared_ptr<afrl::cmasi::Waypoint> wp(new afrl::cmasi::Waypoint ());
                    wp->setNumber(m_waypoints.size() + 1);
                    wp->setNextWaypoint(wp->getNumber());
                    wp->setSpeed(22.0);  // TODO: get from AirVehicleConfiguration

                    if (!currentXmlNode.attribute("Latitude").empty())
                    {
                        wp->setLatitude(currentXmlNode.attribute("Latitude").as_double());
                    }
                    if (!currentXmlNode.attribute("Longitude").empty())
                    {
                        wp->setLongitude(currentXmlNode.attribute("Longitude").as_double());
                    }
                    if (!currentXmlNode.attribute("Altitude").empty())
                    {
                        wp->setAltitude(currentXmlNode.attribute("Altitude").as_double());
                    }

                    std::cerr << "Found waypoint : " << wp->toXML() << '\n';

                    m_waypoints.push_back (wp);
                }
                // read a waypoint via cell id
                if (std::string("WaypointCell") == currentXmlNode.name())
                {
                    if (!currentXmlNode.attribute("X").empty() &&
                        !currentXmlNode.attribute("Y").empty() &&
                        !currentXmlNode.attribute("Altitude").empty())
                    {
                        auto nextPosition = CellToGps(currentXmlNode.attribute("X").as_int(),
                                                      currentXmlNode.attribute("Y").as_int());

                        std::shared_ptr<afrl::cmasi::Waypoint> wp(new afrl::cmasi::Waypoint ());
                        wp->setNumber(m_waypoints.size() + 1);
                        wp->setNextWaypoint(wp->getNumber());
                        wp->setSpeed(22.0);  // TODO: get from AirVehicleConfiguration
                        wp->setLatitude(nextPosition.lat());
                        wp->setLongitude(nextPosition.lng());                    
                        wp->setAltitude(currentXmlNode.attribute("Altitude").as_double());

                        std::cerr << "Found waypoint cell id : ("
                                  << currentXmlNode.attribute("X").as_int() << ','
                                  << currentXmlNode.attribute("Y").as_int() << ")\n";
                        std::cerr << "Found waypoint cell : " << wp->toXML() << '\n';

                        m_waypoints.push_back (wp);
                    }
                }
            }    
        }
    
        bool CollisionAvoidanceService::configure(const pugi::xml_node& serviceXmlNode)
        {
            //-- set pointer to waypoints
            node_uav::wpPtr = &m_waypoints;
        
            //-- read arguments from XML file
            read_arguments (serviceXmlNode);
            //check_argument_sanity ();

            std::cout << "CollisionAvoidanceService configured for id " << settings.id << "...\n";
      
            //-- Initialize commonly used local variables
            id = settings.id;
            num_processes = processes;

            /******************************************************************/
            //-- Invoking constructors
            /******************************************************************/
            if(node_name == "uav" && role_name == "Uav") node_uav::node_uav_role_Uav::constructor ();

            //-- Defining thread functions for MADARA
            if(node_name == "uav" && role_name == "Uav")
                knowledge.define_function ("REMODIFY_INPUT_GLOBALS",
                                           node_uav::node_uav_role_Uav::REMODIFY_INPUT_GLOBALS);
            knowledge.define_function ("node_uav_role_Uav_COLLISION_AVOIDANCE_REMODIFY_BARRIERS",
                                       node_uav::node_uav_role_Uav::REMODIFY_BARRIERS_COLLISION_AVOIDANCE);
            knowledge.define_function ("node_uav_role_Uav_COLLISION_AVOIDANCE_REMODIFY_GLOBALS",
                                       node_uav::node_uav_role_Uav::REMODIFY_GLOBALS_COLLISION_AVOIDANCE);
            knowledge.define_function ("node_uav_role_Uav_COLLISION_AVOIDANCE_PULL",
                                       node_uav::node_uav_role_Uav::thread0_PULL);
            knowledge.define_function ("node_uav_role_Uav_COLLISION_AVOIDANCE_PUSH",
                                       node_uav::node_uav_role_Uav::thread0_PUSH);
            knowledge.define_function ("node_uav_role_Uav_COLLISION_AVOIDANCE",
                                       node_uav::node_uav_role_Uav::thread0);

            //-- Synchronize to make sure all nodes are up
            /*
              knowledge.define_function ("sync_inputs", dmpl::sync_inputs);
              Algo *syncInputsAlgo = new Algo(1000000, "sync_inputs", &knowledge);
              syncInputsAlgo->start(m_threader);
              {
              syncPhase = 1;
              for(;;) {
              size_t flag = 1;
              for(size_t i = 0;i < 2; ++i)
              if(startSync[i] < syncPhase) { flag = 0; break; }
              if(flag) break;
              sleep(0.2);
              }
              syncPhase = 2;
              for(;;) {
              size_t flag = 1;
              for(size_t i = 0;i < 2; ++i)
              if(startSync[i] < syncPhase) { flag = 0; break; }
              if(flag) break;
              sleep(0.2);
              }
              }
            */

            //-- Initializing platform
            engine::KnowledgeMap platform_args;
      
            //-- Creating algorithms
            std::vector<Algo *> algos;
            Algo *algo;
            std::cerr << "node_name = " << node_name << " role_name = " << role_name << '\n';
            if(node_name == "uav" && role_name == "Uav") {
                syncPartnerIds["node_uav_role_Uav_COLLISION_AVOIDANCE"][0] = {1};
                syncPartnerIds["node_uav_role_Uav_COLLISION_AVOIDANCE"][1] = {0};
                algo = new SyncAlgo(100000, "node_uav_role_Uav_COLLISION_AVOIDANCE", "COLLISION_AVOIDANCE", &knowledge, platform_name, &platform_args);
                algos.push_back(algo);
            }

            //-- start threads and simulation
            for(int i = 0; i < algos.size(); i++)
                algos[i]->start(m_threader);
            std::stringstream buffer;
            buffer << "(S" << id << ".init = 1) && S0.init";
            for(unsigned int i = 1; i < num_processes; ++i)
                buffer << " && S" << i << ".init";
            std::string expression = buffer.str ();
            madara::knowledge::CompiledExpression compiled;
            compiled = knowledge.compile (expression);
            std::cerr << "waiting for " << num_processes << " agent(s) to come online..." << std::endl;
            knowledge.wait (compiled);

            knowledge.set("begin_sim", "1");
            std::cerr << "*** AGENT " << id << " READY ***" << std::endl;

            //-- subscribe to private messages from
            //-- WaypointPlanManagerService containing waypoints
            addSubscriptionAddress(STRING_XML_COLLISION_AVOIDANCE);
        
            return true;
        }

        bool CollisionAvoidanceService::initialize()
        {
            bool bSuccess(true);
            return (bSuccess);
        };

        bool CollisionAvoidanceService::terminate()
        {
            return true;
        }

        bool
        CollisionAvoidanceService::
        processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage>
                                   receivedLmcpMessage)
        {
            if (receivedLmcpMessage->m_object->getLmcpTypeName() == "MissionCommand")
            {
                if (std::static_pointer_cast<afrl::cmasi::MissionCommand> (receivedLmcpMessage->m_object)->getVehicleID() == m_entityId)
                {
                    std::cerr << "received private message from WaypointPlanManagerService ...\n";
                    std::cerr << receivedLmcpMessage->m_object->toXML() << '\n';
                    std::shared_ptr<afrl::cmasi::MissionCommand> ptr_MissionCommand(static_cast<afrl::cmasi::MissionCommand*> (receivedLmcpMessage->m_object.get())->clone());

                    //-- update list of waypoints. make sure you get the lock.
                    {
                        std::lock_guard<std::mutex> lockGuard(node_uav::wpLock);

                        for(auto x : ptr_MissionCommand->getWaypointList())
                        {
                            if(m_waypoints.empty() || m_waypoints.back()->getNumber() < x->getNumber())
                            {
                                m_waypoints.push_back(std::shared_ptr<afrl::cmasi::Waypoint>(x->clone()));
                            }
                        }
                        std::cerr << "Updated waypoints : " << m_waypoints.size() << '\n';
                    }
                }
            
            }

            return false;
        }
    }
}

/********************************************************************/
//-- End of generated code
/********************************************************************/
