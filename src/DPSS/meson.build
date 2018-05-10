cpp_args_dpss = cpp_args

if cpp.get_id() == 'msvc'
  cpp_args_dpss += [
    '-DDPSS_STATIC',
  ]
endif

lib_dpss = static_library(
  'dpss',
  [
    'CoordinateConversions.cpp',
    'DRand.cpp',
    'Dpss.cpp',
    'DpssApi.cpp',
    'DpssDataTypes.cpp',
    'DpssUtilities.cpp',
    'PlanOffset.cpp',
    'PlanQuickly.cpp',
    'PlanPrecisely.cpp',
    'SegmentMap.cpp',
    'SensorSteering.cpp',
  ],
  cpp_args: cpp_args_dpss,
  include_directories: include_directories(
    '../../src/Includes',
    '../../src/Utilities',
  ),
)
