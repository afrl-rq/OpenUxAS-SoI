srcs_services = [
	'LoiterLeash.cpp',
  '00_ServiceTemplate.cpp',
  '01_HelloWorld.cpp',
  'AutomationDiagramDataService.cpp',
  'AssignmentTreeBranchBoundBase.cpp',
  'AssignmentTreeBranchBoundService.cpp',
  'AutomationRequestValidatorService.cpp',
  'BatchSummaryService.cpp',
  'MessageLoggerDataService.cpp',
  'OperatingRegionStateService.cpp',
  'OsmPlannerService.cpp',
  'PlanBuilderService.cpp',
  'RouteAggregatorService.cpp',
  'RoutePlannerService.cpp',
  'SendMessagesService.cpp',
  'SensorManagerService.cpp',
  'SerialAutomationRequestTestService.cpp',
  'ServiceBase.cpp',
  'ServiceManager.cpp',
  'Test_SimulationTime.cpp',
  'RoutePlannerVisibilityService.cpp',
  'WaypointPlanManagerService.cpp',
  'SimpleWaypointPlanManagerService.cpp',
]

inc_3rd = include_directories('.')
if get_option('internal_3rd_libraries')
  inc_3rd = include_directories(
      '../../3rd/cppzmq-4.2.2',
      '../../3rd/zeromq-4.2.3/include',
      '../../3rd/czmq-4.0.2/include',
      '../../3rd/zyre-2.0.0/include',
      '../../3rd/sqlite-amalgamation-3120200',
      '../../3rd/SQLiteCpp-1.3.1/include',
      '../../3rd/zlib-1.2.8/contrib/minizip',
      '../../3rd/zlib-1.2.8',
    )
endif


incs_services = [
  include_directories(
    '../../src/Utilities',
    '../../resources/AutomationDiagramDataService',
    '../../src/Communications',
    '../../src/Includes',
    '../../src/Services',
    '../../src/VisilibityLib',
    '../../src/Plans',
    '../../src/DPSS',
    '../../src/Tasks',
    '../../3rd/PugiXML/src',
    '../../3rd/serial-1.2.1/include',
    '../../3rd/TinyGPS',
  ),
  inc_3rd,
  incs_lmcp,
]

if get_option('afrl_internal')
  incs_services += [incs_services_internal]
else
  srcs_services_internal = files()
endif

cpp_args = []
cpp = meson.get_compiler('cpp')

if cpp.get_id() == 'msvc'
  cpp_args += [
  	'/std:c++14',
	'-DZMQ_STATIC',
	'-DCZMQ_STATIC',
	'-DZYRE_STATIC',
	'-DLIBZMQ_STATIC',
	'-DLIBCZMQ_STATIC',
	'-DLIBZYRE_STATIC',
  ]
else
  cpp_args += [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ]
endif

dep_3rd = []
if get_option('internal_3rd_libraries')
  dep_3rd = [dep_boost]
endif

lib_services = static_library(
  'services',
  srcs_services,
  srcs_services_internal,
  dependencies: dep_3rd,
  cpp_args: cpp_args,
  include_directories: incs_services,
)
