cpp_args = []
cpp = meson.get_compiler('cpp')

if cpp.get_id() == 'msvc'
  cpp_args += [
    '/std:c++14',
	'-DDPSS_STATIC',
  ]
else
  cpp_args += [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
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
  cpp_args: cpp_args,
  include_directories: include_directories(
    '../../src/Includes',
    '../../src/Utilities',
  ),
)
