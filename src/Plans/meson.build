dep_3rd = []
if get_option('internal_3rd_libraries')
  dep_3rd = [dep_boost]
endif


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
  dependencies: dep_3rd,
  cpp_args: [
    '-std=c++11',
  ],
  include_directories: [
    include_directories(
      '../../src/Includes',
      '../../src/Utilities',
      '../../src/VisilibityLib',
      '../../3rd/PugiXML/src',
    ),
    incs_lmcp,
  ],
)
