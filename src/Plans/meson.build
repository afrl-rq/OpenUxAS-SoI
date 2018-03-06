lib_plans = static_library(
  'plans',
  [
    'CGrid.cpp',
    'Edge.cpp',
    'Polygon.cpp',
    'Position.cpp',
    'Trajectory.cpp',
    'VisibilityGraph.cpp',
    'Waypoint.cpp',
  ],
  dependencies: [
    dep_boost,
    dep_pugixml,
  ],
  cpp_args: cpp_args,
  include_directories: [
    include_directories(
      '../../src/Includes',
      '../../src/Utilities',
      '../../src/VisilibityLib',
    ),
    incs_lmcp,
  ],
)
