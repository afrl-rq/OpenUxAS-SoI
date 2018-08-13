project('PugiXML', 'cpp')

os = target_machine.system()
if os.startswith('linux')
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

if meson.get_compiler('cpp').get_id() == 'msvc'
  cpp_args_pugixml = [
    '/std:c++14',
  ]
else
  cpp_args_pugixml = [
    '-std=c++11',
  ]
endif

lib = static_library(
  'pugixml',
  'src/pugixml.cpp',
  cpp_args: cpp_args_pugixml,
)

dep = declare_dependency(
  link_with: lib,
  include_directories: include_directories(
    'src',
  ),
)
