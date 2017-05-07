srcs_tasks = [
  '00_TaskTemplate.cpp',
  'AngledAreaSearchTaskService.cpp',
  'AssignmentCoordinatorTaskService.cpp',
  'BlockadeTaskService.cpp',
  'CmasiAreaSearchTaskService.cpp',
  'CmasiLineSearchTaskService.cpp',
  'CmasiPointSearchTaskService.cpp',
  'CommRelayTaskService.cpp',
  'CordonTaskService.cpp',
  'EscortTaskService.cpp',
  'ImpactLineSearchTaskService.cpp',
  'ImpactPointSearchTaskService.cpp',
  'MultiVehicleWatchTaskService.cpp',
  'OverwatchTaskService.cpp',
  'PatternSearchTaskService.cpp',
  'TaskManagerService.cpp',
  'TaskServiceBase.cpp',
  'TaskTrackerService.cpp',
]

incs_tasks = [
  '../../src/Includes',
  '../../src/Services',
  '../../src/Communications',
  '../../src/Utilities',
  '../../src/Plans',
  '../../src/LMCP',
  '../../src/DPSS',
  '../../src/VisilibityLib',
  '../../3rd/PugiXML/src',
  '../../cppzmq-4.2.1',
  '../../zeromq-4.1.1/include',
  '../../boost_1_64_0',
]

if get_option('afrl_internal')
  subdir('afrl_internal')
else
  srcs_tasks_internal = files()
endif

lib_tasks = static_library(
  'tasks',
  srcs_tasks,
  srcs_tasks_internal,
  cpp_args: [
    '-std=c++11',
  ],
  include_directories: include_directories(incs_tasks),
)
