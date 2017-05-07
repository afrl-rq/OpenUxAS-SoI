project('Plans', 'cpp')

os = target_machine.system()
if os == 'linux'
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

lib = static_library('plans', [
	'CGrid.cpp',
	'Edge.cpp',
	'Polygon.cpp',
	'Position.cpp',
	'Trajectory.cpp',
	'VisibilityGraph.cpp',
	'Waypoint.cpp',
	],
	cpp_args: [
		'-std=c++11',
	],
	include_directories: include_directories(
		'../../src/Includes',
		'../../src/Utilities',
		'../../src/VisilibityLib',
		'../../src/LMCP',
#		'../../pugixml-1.2/src',
		'../../3rd/PugiXML/src',
                '../../boost_1_64_0',
	),
)
