project('UxAS', 'c', 'cpp', subproject_dir: '3rd')

cpp = meson.get_compiler('cpp')
conf = configuration_data()
os = target_machine.system()

if cpp.get_id() == 'msvc'
  cpp_args = [
    '/std:c++14',
  ]
else
  cpp_args = [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ]
endif

link_args = []

if os.startswith('linux')
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
  link_args += ['-lrt', '-ldl']
elif os == 'darwin'
  link_args += ['-ldl']
elif os == 'windows'
  link_args += []
endif

if get_option('force_dep_download')
  dep_zeromq    = subproject('zeromq').get_variable('dep')
  dep_czmq      = subproject('czmq').get_variable('dep')
  dep_cppzmq    = subproject('cppzmq').get_variable('dep')
  dep_zyre      = subproject('zyre').get_variable('dep')
  dep_sqlite3   = subproject('sqlite3').get_variable('dep')
  dep_sqlitecpp = subproject('sqlitecpp').get_variable('dep')
  dep_zlib      = subproject('zlib').get_variable('dep')
  dep_minizip   = subproject('minizip').get_variable('dep')
else
  # https://github.com/zeromq/{zeromq, czmq, cppzmq, zyre}
  dep_zeromq = dependency(
    'libzmq',
    fallback: ['zeromq', 'dep'],
  )

  dep_czmq = dependency(
    'libczmq',
    fallback: ['czmq', 'dep'],
  )

  if cpp.has_header('zmq.hpp')
    # cppzmq is a header-only dependency, so if we already have the
    # header in place, we don't need to actually change anything
    dep_cppzmq = [] #declare_dependency()
  else
    dep_cppzmq = subproject('cppzmq').get_variable('dep')
  endif

  dep_zyre = dependency(
    'libzyre',
    fallback: ['zyre', 'dep'],
  )

  # https://www.sqlite.org/src
  dep_sqlite3 = dependency(
    'sqlite3',
    required: false,
  )

  # force native build of SQLite3 if load extension function is unavailable
  # required for SQLiteCpp
  if not dep_sqlite3.found() or not cpp.has_function('sqlite3_enable_load_extension', dependencies: dep_sqlite3)
    dep_sqlite3 = subproject('sqlite3').get_variable('dep')
  endif

  # SQLiteCpp is unfortunately not packaged with pkg-config
  lib_sqlitecpp = cpp.find_library('SQLiteCpp', required: false)
  if lib_sqlitecpp.found() and cpp.has_header('SQLiteCpp/SQLiteCpp.h')
    dep_sqlitecpp = lib_sqlitecpp
  else
    # https://github.com/SRombauts/SQLiteCpp
    dep_sqlitecpp = subproject('sqlitecpp').get_variable('dep')
  endif

  # https://github.com/madler/zlib
  dep_zlib = dependency(
    'zlib',
    fallback: ['zlib', 'dep'],
  )

  # https://github.com/nmoinvaz/minizip
  dep_minizip = dependency(
    'minizip',
    fallback: ['minizip', 'dep'],
  )
endif

# handle boost carefully
dep_boost = dependency(
  'boost',
  modules: ['date_time', 'filesystem', 'regex', 'system'],
  fallback: ['boost', 'dep'],
)

# https://github.com/mikalhart/TinyGPS
# The TinyGPS repo captured by UxAS does not seem to be available.
# The repo contains *only* version 13, while UxAS uses what appears
# to be version 12. Perhaps contact the author...?
dep_tinygps = subproject('TinyGPS').get_variable('dep')

# https://github.com/wjwwood/serial
dep_serial = subproject('serial-1.2.1').get_variable('dep')

# https://github.com/zeux/pugixml
# No versions of this pugixml repo are compatible.
dep_pugixml = subproject('PugiXML').get_variable('dep')

if get_option('afrl_internal')
  subdir('UxAS-afrl_internal')
endif

deps = [
  dependency('threads'),
  dep_boost,
  dep_zeromq,
  dep_czmq,
  dep_cppzmq,
  dep_zyre,
  dep_sqlite3,
  dep_sqlitecpp,
  dep_zlib,
  dep_minizip,
  dep_tinygps,
  dep_serial,
  dep_pugixml,
]

subdir('src/DPSS')

subdir('src/VisilibityLib')

if not get_option('afrl_internal')
  subdir('src/LMCP')
endif

subdir('src/Communications')

subdir('src/Tasks')

subdir('src/Services')

subdir('src/Utilities')

subdir('src/Plans')

subdir('src/DAIDALUS')

libs = [
  lib_services,
  lib_tasks,
  lib_lmcp,
  lib_uxas_communications,
  lib_utilities,
  lib_visilibity,
  lib_plans,
  lib_dpss,
  lib_daidalus,
]

if get_option('afrl_internal')
  libs += libs_internal
endif

# creates src/Includes/config.h
subdir('src/Includes')

glu_deps = []
# OpenGL, specifically the GLU library
if os == 'darwin'
  # newer MacOS splits out GLU into a separate framework, but we can't
  # ask Meson for the version in order to handle things differently
  glu_deps += [dependency('gl')]
  glu_deps += [dependency('glu', required: false)]
elif os.startswith('linux')
  if not (target_machine.cpu_family() == 'arm')
    glu_deps += [dependency('glu')]
  endif
elif os == 'windows'
  glu_deps += [cpp.find_library('glu32')]
endif

# ensure that required glu functions are available
# note: 'has_function' check cannot reach into windows c libraries
glu_functions = ['gluNewTess', 'gluDeleteTess', 'gluErrorString']
foreach fn : glu_functions
  if os != 'windows' and not cpp.has_function(fn, dependencies: glu_deps)
    error('GLU library functions not found')
  endif
endforeach
deps += glu_deps

if get_option('afrl_internal')
  deps += deps_internal
  link_args += link_args_internal
endif


executable(
  'uxas',
  'src/UxAS_Main.cpp',
  dependencies: deps,
  link_args: link_args,
  cpp_args: cpp_args,
  include_directories: [
    include_directories(
      'src/Utilities',
      'src/Communications',
      'src/Includes',
      'src/Services',
    ),
    incs_lmcp,
  ],
  link_with: libs,
  install: true,
)

subdir('tests')

if get_option('afrl_internal')
  subdir('UxAS-afrl_internal/tests')
endif
