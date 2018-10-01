project('TinyGPS', 'cpp')

os = target_machine.system()
if os.startswith('linux')
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

if meson.get_compiler('cpp').get_id() == 'msvc'
  cpp_args_tinygps = [
    '/std:c++14',
  ]
else
  cpp_args_tinygps = [
    '-std=c++11',
  ]
endif

dep_boost = dependency(
  'boost',
  modules: ['date_time'],
  fallback: ['boost', 'dep'],
)

lib = static_library(
  'tinygps',
  'TinyGPS.cpp',
  cpp_args: cpp_args_tinygps,
  dependencies: dep_boost,
  include_directories: include_directories(
    '../../src/Includes',
    '../../src/Utilities',
  ),
)

dep = declare_dependency(
  link_with: lib,
  include_directories: include_directories(
    '.',
  ),
)
