project('DPSS', 'cpp')

os = target_machine.system()
if os == 'linux'
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

lib = static_library('dpss', [
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
	cpp_args: [
		'-std=c++11',
	],
	include_directories: include_directories(
		'../../src/Includes',
		'../../src/Utilities',
	),
)
