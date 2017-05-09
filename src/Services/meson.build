srcs_services = [
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
  'TcpBridge.cpp',
  'Test_SimulationTime.cpp',
  'RoutePlannerVisibilityService.cpp',
  'WaypointPlanManagerService.cpp',
]

incs_services = [
  include_directories(
    '../../src/Utilities',
    '../../resources/AutomationDiagramDataService',
    '../../src/LMCP',
    '../../src/Communications',
    '../../src/Includes',
    '../../src/Services',
    '../../src/VisilibityLib',
    '../../src/Plans',
    '../../src/DPSS',
    '../../src/Tasks',
    '../../zyre-1.1.0/include',
    '../../cppzmq-4.2.1',
    '../../czmq-3.0.1/include',
    '../../zeromq-4.1.1/include',
    '../../3rd/PugiXML/src',
    '../../SQLiteCpp-1.3.1/include',
    '../../sqlite-amalgamation-3120200',
    '../../serial-1.2.1/include',
    '../../3rd/TinyGPS',
    '../../zlib-1.2.8/contrib/minizip',
    '../../zlib-1.2.8',
  ),
  incs_lmcp,
]

if get_option('afrl_internal')
  incs_services += [incs_services_internal]
else
  srcs_services_internal = files()
endif

lib_services = static_library(
  'services',
  srcs_services,
  srcs_services_internal,
  dependencies: [
    dep_boost,
  ],
  cpp_args: [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ],
  include_directories: incs_services,
)
