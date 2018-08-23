srcs_services = [
  '00_ServiceTemplate.cpp',
  '01_HelloWorld.cpp',
  'AssignmentTreeBranchBoundBase.cpp',
  'AssignmentTreeBranchBoundService.cpp',
  'AutomationDiagramDataService.cpp',
  'AutomationRequestValidatorService.cpp',
  'BatchSummaryService.cpp',
  'LoiterLeash.cpp',
  'MessageLoggerDataService.cpp',
  'OperatingRegionStateService.cpp',
  'OsmPlannerService.cpp',
  'PlanBuilderService.cpp',
  'RouteAggregatorService.cpp',
  'RoutePlannerService.cpp',
  'RoutePlannerVisibilityService.cpp',
  'SendMessagesService.cpp',
  'SensorManagerService.cpp',
  'SerialAutomationRequestTestService.cpp',
  'ServiceBase.cpp',
  'ServiceManager.cpp',
  'SimpleWaypointPlanManagerService.cpp',
  'StatusReportService.cpp',
  'Test_SimulationTime.cpp',
  'WaypointPlanManagerService.cpp',
  'SteeringService.cpp',
]

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
  ),
  incs_lmcp,
]

deps_services = [
  dep_boost,
  dep_cppzmq,
  dep_pugixml,
  dep_sqlite3,
  dep_sqlitecpp,
  dep_zeromq,
]

if get_option('afrl_internal')
  deps_services += deps_services_internal
  incs_services += incs_services_internal
else
  srcs_services_internal = files()
endif

lib_services = static_library(
  'services',
  srcs_services,
  srcs_services_internal,
  dependencies: deps_services,
  cpp_args: cpp_args,
  include_directories: incs_services,
)
