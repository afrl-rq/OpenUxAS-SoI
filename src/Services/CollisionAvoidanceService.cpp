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
Reference<unsigned int> id(knowledge, ".id");
Reference<unsigned int>  num_processes(knowledge, ".num_processes");
engine::KnowledgeUpdateSettings private_update (true);

//-- used to synchronize and make sure that all nodes are up
ArrayReference<unsigned int, 2> startSync(knowledge, "startSync");
Reference<unsigned int> syncPhase(knowledge, ".syncPhase");

KnowledgeRecord
sync_inputs (engine::FunctionArguments & args, engine::Variables & vars)
{
  std::string syncStr("REMODIFY_INPUT_GLOBALS () ; startSync.{.id} = .syncPhase");
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
//-- handle arguments from the command line
/********************************************************************/
void handle_arguments (int argc, char ** argv)
{
  for (int i = 1; i < argc; ++i)
  {
    std::string arg1 (argv[i]);

    if (arg1 == "-m" || arg1 == "--multicast")
    {
      if (i + 1 < argc)
      {
        settings.hosts.push_back (argv[i + 1]);
        settings.type = madara::transport::MULTICAST;
      }
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-p" || arg1 == "--platform")
    {
      if (i + 1 < argc)
      {
        tokenize(std::string(argv[i + 1]), platform_params, ":");
        platform_name = (platform_params[0]);
      }
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-b" || arg1 == "--broadcast")
    {
      if (i + 1 < argc)
      {
        settings.hosts.push_back (argv[i + 1]);
        settings.type = madara::transport::BROADCAST;
      }
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-u" || arg1 == "--udp")
    {
      if (i + 1 < argc)
      {
        settings.hosts.push_back (argv[i + 1]);
        settings.type = madara::transport::UDP;
      }
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-o" || arg1 == "--host")
    {
      if (i + 1 < argc)
        host = argv[i + 1];
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-d" || arg1 == "--domain")
    {
      if (i + 1 < argc) {
        settings.write_domain = argv[i + 1];
        settings.add_read_domain(argv[i + 1]);
      } else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-i" || arg1 == "--id")
    {
      if (i + 1 < argc)
      {
        std::stringstream buffer (argv[i + 1]);
        buffer >> settings.id;
        if(settings.id < 0 || settings.id >= 2) {
          std::cerr << "ERROR: Invalid node id: " << settings.id 
                    << "  valid range: [0, 1]" << std::endl;
          ::exit(1);
        }
        if(settings.id == 0) { node_name = "uav"; role_name = "Uav"; }
        if(settings.id == 1) { node_name = "uav"; role_name = "Uav"; }
        if(settings.id == 2) { node_name = "uav"; role_name = "Uav"; }
      }
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-l" || arg1 == "--level")
    {
      if (i + 1 < argc)
      {
        int log_level = 0;
        std::stringstream buffer (argv[i + 1]);
        buffer >> log_level;
        madara::logger::global_logger->set_level(log_level);
        gams::loggers::global_logger->set_level(log_level);
      }
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "--drop-rate")
    {
      if (i + 1 < argc)
      {
        double drop_rate;
        std::stringstream buffer (argv[i + 1]);
        buffer >> drop_rate;
        std::cerr << "drop_rate: " << drop_rate << std::endl;
        settings.update_drop_rate (drop_rate,
          madara::transport::PACKET_DROP_PROBABLISTIC);
      }
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-e" || arg1 == "--expect-log")
    {
      if (i + 1 < argc)
      {
        expect_file.open(argv[i + 1], ios::out | ios::trunc);
      }
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-f" || arg1 == "--logfile")
    {
      if (i + 1 < argc)
      {
        ::madara::logger::global_logger->clear();
        ::madara::logger::global_logger->add_file(argv[i + 1]);
      }
      else goto WRONG_ARG;
      ++i;
    }
    else if (arg1 == "-r" || arg1 == "--reduced")
    {
      settings.send_reduced_message_header = true;
    }
    else if (arg1 == "-dbg" || arg1 == "--debug")
    {
      dmpl::debug = true;
    }
    else if (arg1 == "--write-fd")
    {
      if (i + 1 < argc)
      {
        std::stringstream buffer (argv[i + 1]);
        buffer >> write_fd;
      }
      else goto WRONG_ARG;
      ++i;
    }

    //-- Providing init for input variable x
    else if (arg1 == "--var_x")
    {
      if (i + 1 < argc)
      {
        std::stringstream buffer (argv[i + 1]);
        if(node_name == "uav" && role_name == "Uav")
          buffer >> node_uav::var_init_x;
        else throw std::runtime_error
             ("ERROR : no input variable x for node and role combination : ("
              + node_name + " , " + role_name + ")");
      }
      
      else goto WRONG_ARG;
      ++i;
    }

    //-- Providing init for input variable xf
    else if (arg1 == "--var_xf")
    {
      if (i + 1 < argc)
      {
        std::stringstream buffer (argv[i + 1]);
        if(node_name == "uav" && role_name == "Uav")
          buffer >> node_uav::var_init_xf;
        else throw std::runtime_error
             ("ERROR : no input variable xf for node and role combination : ("
              + node_name + " , " + role_name + ")");
      }
      
      else goto WRONG_ARG;
      ++i;
    }

    //-- Providing init for input variable y
    else if (arg1 == "--var_y")
    {
      if (i + 1 < argc)
      {
        std::stringstream buffer (argv[i + 1]);
        if(node_name == "uav" && role_name == "Uav")
          buffer >> node_uav::var_init_y;
        else throw std::runtime_error
             ("ERROR : no input variable y for node and role combination : ("
              + node_name + " , " + role_name + ")");
      }
      
      else goto WRONG_ARG;
      ++i;
    }

    //-- Providing init for input variable yf
    else if (arg1 == "--var_yf")
    {
      if (i + 1 < argc)
      {
        std::stringstream buffer (argv[i + 1]);
        if(node_name == "uav" && role_name == "Uav")
          buffer >> node_uav::var_init_yf;
        else throw std::runtime_error
             ("ERROR : no input variable yf for node and role combination : ("
              + node_name + " , " + role_name + ")");
      }
      
      else goto WRONG_ARG;
      ++i;
    }
    else
    {
      WRONG_ARG:
      std::cerr << "Illegal argument : " << arg1 << '\n'
                << "Usage : " << argv[0] << " <options> <dmpl-file>\n"
                << "Options :\n" <<
        " [-p|--platform type]     platform for loop (vrep, dronerk)\n"\
        " [-b|--broadcast ip:port] the broadcast ip to send and listen to\n"\
        " [-d|--domain domain]     the knowledge domain to send and listen to\n"\
        " [-e|--expect-log file]   file to log variables related to 'expect' clauses\n"\
        " [-f|--logfile file]      log to a file\n"\
        " [-i|--id id]             the id of this agent (should be non-negative)\n"\
        " [-l|--level level]       the logger level (0+, higher is higher detail)\n"\
        " [-m|--multicast ip:port] the multicast ip to send and listen to\n"\
        " [-mb|--max-barrier-time time] time in seconds to barrier for other processes\n"\
        " [-o|--host hostname]     the hostname of this process (def:localhost)\n"\
        " [-r|--reduced]           use the reduced message header\n"\
        " [-dbg|--debug]           print debug messages\n"\
        " [-u|--udp ip:port]       the udp ips to send to (first is self to bind to)\n"\
        " [--var_x] sets the initial value of variable x\n"\
        " [--var_xf] sets the initial value of variable xf\n"\
        " [--var_y] sets the initial value of variable y\n"\
        " [--var_yf] sets the initial value of variable yf\n"\
        ;
      ::exit (1);
    }
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
    if (((thread0_x == thread0_xf) && (thread0_y == thread0_yf)))
    {
      if ((thread0_missionOver[id] == Integer (0)))
      {
        thread0_missionOver[id] = Integer (1);
        {
          (void) (std::cerr  << "node " << id << " completed mission ...\n");
        }
      }
      if (((id == 0 && ((thread0_missionOver[1] == Integer (0)) || (thread0_missionOver[2] == Integer (0)))) || 
        (id == 1 && ((thread0_missionOver[0] == Integer (0)) || (thread0_missionOver[2] == Integer (0)))) || 
        (id == 2 && ((thread0_missionOver[0] == Integer (0)) || (thread0_missionOver[1] == Integer (0))))))
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
        if (((id == 0 && ((thread0_lock[1][thread0_xp][thread0_yp] != Integer (0)) || (thread0_lock[2][thread0_xp][thread0_yp] != Integer (0)))) || 
          (id == 1 && ((thread0_lock[2][thread0_xp][thread0_yp] != Integer (0))))))
        {
          return Integer(0);
        }
        thread0_state = MOVE;
      }
      else
      {
        if ((thread0_state == MOVE))
        {
          if ((GRID_MOVE (thread0_xp, thread0_yp, Integer (1))))
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

  //-- Declare local (parameter and temporary) variables


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
    knowledge_->expand_statement (_exec_func + " (); ++" + mbarrier + ".{.id}"));
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
      knowledge_->evaluate ("++" + mbarrier + ".{.id}", wait_settings); 
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
    
    bool CollisionAvoidanceService::configure(const pugi::xml_node& serviceXmlNode)
    {
      std::cout << "Collision Avoidance Service configured ...\n";
      return true;
        
      //-- TBD
      settings.type = madara::transport::MULTICAST;

      /*
        platform_init_fns["vrep"] = init_vrep;
        platform_init_fns["vrep-uav"] = init_vrep;
        platform_init_fns["vrep-quad"] = init_vrep;
        platform_init_fns["vrep-heli"] = init_vrep;
        platform_init_fns["vrep-ant"] = init_vrep;
        platform_init_fns["vrep-uav-laser"] = init_vrep;
        platform_init_fns["vrep-quad-laser"] = init_vrep;
      */
  
      //-- handle any command line arguments and check their sanity
      //handle_arguments (argc, argv);
      check_argument_sanity ();

      if (settings.hosts.size () == 0)
        {
          //-- setup default transport as multicast
          settings.hosts.push_back (default_multicast);
          if (dmpl::debug) {
            settings.add_receive_filter (madara::filters::log_aggregate);
            settings.add_send_filter (madara::filters::log_aggregate);
          }
        }

      settings.queue_length = 1000000;
      settings.set_deadline(1);

      //-- configure the knowledge base with the transport settings
      knowledge.attach_transport(host, settings);

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
      knowledge.define_function ("sync_inputs", dmpl::sync_inputs);
      threads::Threader threader(knowledge);
      Algo *syncInputsAlgo = new Algo(1000000, "sync_inputs", &knowledge);
      syncInputsAlgo->start(threader);
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

      //-- Initializing platform
      engine::KnowledgeMap platform_args;
      /*
        PlatformInitFns::iterator init_fn = platform_init_fns.find(platform_name);
        if(init_fn != platform_init_fns.end())
        init_fn->second(platform_params, knowledge, platform_args);
        else
        init_vrep(platform_params, knowledge, platform_args);
      */
  
      //-- Initializing simulation
      if(node_name == "uav" && role_name == "Uav") {
        knowledge.define_function ("initialize_platform", node_uav::node_uav_role_Uav::base_StartingPosition);
      }
      knowledge.evaluate("initialize_platform ()");

      //-- Creating algorithms
      std::vector<Algo *> algos;
      Algo *algo;
      if(node_name == "uav" && role_name == "Uav") {
        syncPartnerIds["node_uav_role_Uav_COLLISION_AVOIDANCE"][0] = {1,2};
        syncPartnerIds["node_uav_role_Uav_COLLISION_AVOIDANCE"][1] = {0,2};
        syncPartnerIds["node_uav_role_Uav_COLLISION_AVOIDANCE"][2] = {0,1};
        algo = new SyncAlgo(100000, "node_uav_role_Uav_COLLISION_AVOIDANCE", "COLLISION_AVOIDANCE", &knowledge, platform_name, &platform_args);
        algos.push_back(algo);
      }

      //-- start threads and simulation
      for(int i = 0; i < algos.size(); i++)
        algos[i]->start(threader);
      std::stringstream buffer;
      buffer << "(vrep_ready = 1) && (S" << id << ".init = S" << id << ".init) && S0.init";
      for(unsigned int i = 1; i < num_processes; ++i)
        buffer << " && S" << i << ".init";
      std::string expression = buffer.str ();
      madara::knowledge::CompiledExpression compiled;
      compiled = knowledge.compile (expression);
      std::cerr << "waiting for " << num_processes << " agent(s) to come online..." << std::endl;
      knowledge.wait (compiled);

      knowledge.set("begin_sim", "1");
      std::cerr << "*** AGENT " << id << " READY ***" << std::endl;

      //-- wait for all threads to terminate
      threader.wait();
  
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
