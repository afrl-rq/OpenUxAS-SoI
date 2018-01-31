project('TinyGPS', 'cpp')

os = target_machine.system()
if os.startswith('linux')
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

lib = static_library(
  'tinygps',
  [
    'TinyGPS.cpp',
  ],
    cpp_args: [
    '-std=c++11',
  ],
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
