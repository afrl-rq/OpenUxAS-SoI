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

inc_3rd = include_directories('.')
if get_option('internal_3rd_libraries')
  inc_3rd = include_directories(
    )
endif


incs_tasks = [
  include_directories(
    '../../src/Includes',
    '../../src/Services',
    '../../src/Communications',
    '../../src/Utilities',
    '../../src/Plans',
    '../../src/DPSS',
    '../../src/VisilibityLib',
  ),
  inc_3rd,
  incs_lmcp,
]

dep_3rd = []
if get_option('internal_3rd_libraries')
  dep_3rd = [dep_boost]
endif

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
    dep_cppzmq,
    dep_pugixml,
  ],
  cpp_args: cpp_args,
  include_directories: incs_tasks
)
