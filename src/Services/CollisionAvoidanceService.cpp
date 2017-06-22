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

  for(int i = 0;i < 150;++i) printf("\n");
  
  printf("round = %d : id = %d\n", ++roundNum, id);
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

namespace
{
    //-- minimum and maximum latitide and longitude of the visible
    //-- map area
    const double LAT_MIN = 45.296;
    const double LAT_MAX = 45.35;
    const double LNG_MIN = -121.02;
    const double LNG_MAX = -120.91;
    const double CELL_LAT = (LAT_MAX - LAT_MIN) / 9;
    const double CELL_LNG = (LNG_MAX - LNG_MIN) / 9;

    //-- a cell id -- pair of X and Y coordinates
    typedef std::pair<int,int> Cell;
    
    //-- function to convert from a position to cell coordinates
    Cell GpsToCell(double lat, double lng)
    {
        double cellx = (lng - (LNG_MIN - CELL_LNG / 2)) / CELL_LNG;
        int icellx = (int)(floor(cellx));
        double celly = (lat - (LAT_MIN - CELL_LAT / 2)) / CELL_LAT;
        int icelly = (int)(floor(celly));
        return Cell(cellx, celly);
    }

    //-- return the GPS location of the center of a cell.
    gams::pose::Position CellToGps(int x, int y)
    {
        gams::pose::Position res(uxas::service::GamsService::frame());
        res.lng(LNG_MIN + x * CELL_LNG);
        res.lat(LAT_MIN + y * CELL_LAT);
        res.alt(700);
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
//-- Defining program-specific constants
/********************************************************************/
#define BottomY -2.25
#define BottomZ 0.0
#define LeftX -2.25
#define MOVE 4
#define MSG_MARKER "message: "
#define NEXT 1
#define REQUEST 2
#define RightX 2.25
#define TopY 2.25
#define TopZ 2.5
#define WAITING 3
#define X 10
#define Y 10
#define Z 10

/********************************************************************/
//-- Begin defining variables for node uav
/********************************************************************/

// begin node_uav namespace
namespace node_uav
{

/********************************************************************/
//-- Defining global variables at node scope
/********************************************************************/
ArrayReference<_Bool, 2, 10, 10> lock(knowledge, "lock");
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

//-- pointer to list of waypoints
gams::pose::Positions *wpPtr = NULL;
    
//-- id of next waypoint to be reached
short nextWpId = 0;
    
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
ArrayReference<Proactive<_Bool, CachedReference>, 2, 10, 10> thread0_lock(knowledge, "lock");
ArrayReference<Proactive<_Bool, CachedReference>, 2> thread0_missionOver(knowledge, "missionOver");

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
base_StartingPosition (engine::FunctionArguments & args, engine::Variables & vars);
KnowledgeRecord
thread0_PULL (engine::FunctionArguments & args, engine::Variables & vars);
KnowledgeRecord
thread0_PUSH (engine::FunctionArguments & args, engine::Variables & vars);
KnowledgeRecord
thread0 (engine::FunctionArguments & args, engine::Variables & vars);
KnowledgeRecord
thread0_COLLISION_AVOIDANCE (engine::FunctionArguments & args, engine::Variables & vars);
KnowledgeRecord
thread0_NEXT_XY (engine::FunctionArguments & args, engine::Variables & vars);
} // end node_uav_role_Uav namespace

} // end node_uav namespace

} // end dmpl namespace


/********************************************************************/
//-- GAMS variables and functions
/********************************************************************/

#include "GamsPlatformUXAS.hpp"

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
//-- @InitSim
KnowledgeRecord
base_StartingPosition (engine::FunctionArguments & args, engine::Variables & vars)
{

  //-- Declare local (parameter and temporary) variables


  //-- Begin function body
  {
    (void) (GRID_INIT ());
  }
  {
    (void) (GRID_PLACE (x, y, Integer (1)));
  }

  //-- Insert return statement, in case user program did not
  return Integer(0);
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


  //-- Begin function body
  {
    (void) (std::cerr  << MSG_MARKER << "id = " << id << " X = " << X << " Y = " << Y << " x = " << thread0_x << " y = " << thread0_y << " state = " << thread0_state << "\n");
  }
  if ((thread0_state == NEXT))
  {
    if ((thread0_x == thread0_xf) && (thread0_y == thread0_yf) && (nextWpId >= wpPtr->size()))
    {
      if ((thread0_missionOver[id] == Integer (0)))
      {
        thread0_missionOver[id] = Integer (1);
        {
          (void) (std::cerr  << "node " << id << " completed mission ...\n");
        }
      }
      if (((id == 0 && ((thread0_missionOver[1] == Integer (0)))) || 
           (id == 1 && ((thread0_missionOver[0] == Integer (0))))))
      {
        return Integer(0);
      }
      {
        (void) (std::cerr << "node " << id << " exited mission with code " << id << '\n'); (::exit (0));
      }
    }
    {
      (void) (thread0_NEXT_XY (
           __strip_const(engine::FunctionArguments(0))
          , vars));
    }
    thread0_state = REQUEST;
  }
  else
  {
    if ((thread0_state == REQUEST))
    {
      if (((id == 1 && ((thread0_lock[0][thread0_xp][thread0_yp] != Integer (0)))) || 
        (id == 2 && ((thread0_lock[0][thread0_xp][thread0_yp] != Integer (0)) || (thread0_lock[1][thread0_xp][thread0_yp] != Integer (0))))))
      {
        return Integer(0);
      }
      thread0_lock[id][thread0_xp][thread0_yp] = Integer (1);
      thread0_state = WAITING;
    }
    else
    {
      if ((thread0_state == WAITING))
      {
          if (((id == 0 && ((thread0_lock[1][thread0_xp][thread0_yp] != Integer (0))))))
        {
          return Integer(0);
        }
        thread0_state = MOVE;
      }
      else
      {
        if ((thread0_state == MOVE))
        {
            gams::pose::Position nextGps = CellToGps(thread0_xp, thread0_yp);
            std::cerr << "GAMS::move " << nextGps << '\n';
            if(uxas::service::GamsService::move (nextGps) != gams::platforms::PLATFORM_ARRIVED)
            {
                return Integer(0);
            }
            thread0_lock[id][thread0_x][thread0_y] = Integer (0);
            thread0_x = thread0_xp;
            thread0_y = thread0_yp;
            thread0_state = NEXT;
        }
      }
    }
  }

  //-- Insert return statement, in case user program did not
  return Integer(0);
}

KnowledgeRecord
thread0_NEXT_XY (engine::FunctionArguments & args, engine::Variables & vars)
{
  std::cerr << "current cell = (" << thread0_x << ',' << thread0_y << ") ...\n";

  //-- Declare local (parameter and temporary) variables
  if((thread0_x == thread0_xf) && (thread0_y == thread0_yf))
  {
      //-- Begin function body
      gams::pose::Position nextPos = (*wpPtr)[nextWpId];
      ++nextWpId;

      auto nextCell = GpsToCell(nextPos.lat(), nextPos.lng());
      thread0_xf = nextCell.first;
      thread0_yf = nextCell.second;

      std::cerr << "next waypoint cell = (" << thread0_xf << ',' << thread0_yf << ") ...\n";
  }
  
  //-- Begin function body
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
  std::cerr << "next cell = (" << thread0_xp << ',' << thread0_yp << ") ...\n";
  
  //-- Insert return statement, in case user program did not
  return Integer(0);
}

/********************************************************************/
//-- Begin constructors for role Uav
/********************************************************************/
void initialize_lock ()
{
  engine::Variables vars;
  lock[id][x][y] = Integer (1);
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
                    double init_lat = currentXmlNode.attribute("init_lat").as_double();
                    double init_lng = currentXmlNode.attribute("init_lng").as_double();
                    auto init_cell = GpsToCell(init_lat, init_lng);
                    std::cerr << "initial cell = " << init_cell.first << "," << init_cell.second << '\n';
                    node_uav::var_init_x = init_cell.first;
                    node_uav::var_init_y = init_cell.second;
                }
            }
            // read a waypoint
            if (std::string("Waypoint") == currentXmlNode.name())
            {
                gams::pose::Position nextPosition (GamsService::frame ());
                
                if (!currentXmlNode.attribute("Latitude").empty())
                {
                    nextPosition.lat(
                        currentXmlNode.attribute("Latitude").as_double());
                }
                if (!currentXmlNode.attribute("Longitude").empty())
                {
                    nextPosition.lng(
                        currentXmlNode.attribute("Longitude").as_double());
                }
                if (!currentXmlNode.attribute("Altitude").empty())
                {
                    nextPosition.alt(
                        currentXmlNode.attribute("Altitude").as_double());
                }

                std::cerr << "Found waypoint : " << nextPosition << '\n';
                m_waypoints.push_back (nextPosition);
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
                    nextPosition.alt(
                        currentXmlNode.attribute("Altitude").as_double());
                    std::cerr << "Found waypoint cell id : ("
                              << currentXmlNode.attribute("X").as_int() << ','
                              << currentXmlNode.attribute("Y").as_int() << ")\n";
                    std::cerr << "Found waypoint cell : " << nextPosition << '\n';
                    m_waypoints.push_back (nextPosition);
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
      return false;
    }
  }
}

/********************************************************************/
//-- End of generated code
/********************************************************************/
