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
  'MustFlyTaskService.cpp',
  'LoiterTaskService.cpp',
  'ImpactPointSearchTaskService.cpp',
  'MultiVehicleWatchTaskService.cpp',
  'OverwatchTaskService.cpp',
  'PatternSearchTaskService.cpp',
  'TaskManagerService.cpp',
  'TaskServiceBase.cpp',
  'TaskTrackerService.cpp',
]

incs_tasks = [
  include_directories(
    '../../src/Includes',
    '../../src/Services',
    '../../src/Communications',
    '../../src/Utilities',
    '../../src/Plans',
    '../../src/DPSS',
    '../../src/VisilibityLib',
    '../../3rd/PugiXML/src',
    '../../3rd/cppzmq-4.2.2',
    '../../3rd/zeromq-4.2.3/include',
  ),
  incs_lmcp,
]

if get_option('afrl_internal')
  incs_tasks += [incs_tasks_internal]
else
  srcs_tasks_internal = files()
endif

cpp_args = []
cpp = meson.get_compiler('cpp')

if cpp.get_id() != 'msvc'
  cpp_args += [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ]
endif

lib_tasks = static_library(
  'tasks',
  srcs_tasks,
  srcs_tasks_internal,
  dependencies: [
    dep_boost,
  ],
  cpp_args: cpp_args,
  include_directories: incs_tasks
)
