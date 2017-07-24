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
  './AutonomyMonitors/VehicleStateListenerService.cpp',
  './AutonomyMonitors/MonitorDB.cpp',
  './AutonomyMonitors/MonitorUtils.cpp',
  './AutonomyMonitors/AutonomyMonitorServiceMain.cpp',
  './AutonomyMonitors/MonitorBase.cpp',
  './AutonomyMonitors/KeepOutZoneMonitor.cpp',
  './AutonomyMonitors/KeepInZoneMonitor.cpp',
  './AutonomyMonitors/VehicleStateMessage.cpp',
  './AutonomyMonitors/PointSearchTaskMonitor.cpp',
  './AutonomyMonitors/LineSearchTaskMonitor.cpp',
  './AutonomyMonitors/AreaSearchTaskMonitor.cpp',
  './AutonomyMonitors/GeometryUtilities.cpp',
  'WaypointPlanManagerService.cpp',
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
    '../../3rd/zyre-1.1.0/include',
    '../../3rd/cppzmq-4.2.1',
    '../../3rd/czmq-3.0.1/include',
    '../../3rd/zeromq-4.1.6/include',
    '../../3rd/PugiXML/src',
    '../../3rd/SQLiteCpp-1.3.1/include',
    '../../3rd/sqlite-amalgamation-3120200',
    '../../3rd/serial-1.2.1/include',
    '../../3rd/TinyGPS',
    '../../3rd/zlib-1.2.8/contrib/minizip',
    './AutonomyMonitors',
    '../../3rd/zlib-1.2.8',
  ),
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
	'-DZMQ_DEFINED_STDINT',
    '-DZMQ_STATIC',
	'-DLIBCZMQ_STATIC',
  ]
else
  cpp_args += [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ]
endif

lib_services = static_library(
  'services',
  srcs_services,
  srcs_services_internal,
  dependencies: [
    dep_boost,
  ],
  cpp_args: cpp_args,
  include_directories: incs_services,
)
