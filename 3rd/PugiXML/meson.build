project('PugiXML', 'cpp')

os = target_machine.system()
if os.startswith('linux')
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

lib = static_library(
  'pugixml',
  'src/pugixml.cpp',
  cpp_args: [
    '-std=c++11',
  ],
)

dep = declare_dependency(
  link_with: lib,
  include_directories: include_directories(
    'src',
  ),
)
