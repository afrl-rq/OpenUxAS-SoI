project('PugiXML', 'cpp')

os = target_machine.system()
if os == 'linux'
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

lib = static_library('pugixml', [
		'src/pugixml.cpp',
	],
	cpp_args: [
		'-std=c++11',
	],
	include_directories: include_directories(
	),
)
