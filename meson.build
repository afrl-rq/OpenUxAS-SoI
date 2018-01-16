project('UxAS', 'c', 'cpp', 'rust', subproject_dir: '3rd')

conf = configuration_data()

link_args = []

os = target_machine.system()

if os.startswith('linux')
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
  link_args += ['-lrt', '-ldl']
elif os == 'darwin'
  link_args += ['-lresolv', '-ldl']
elif os == 'windows'
  link_args += []
endif

sub_fixedbitset = subproject('fixedbitset')
lib_fixedbitset = sub_fixedbitset.get_variable('lib')

sub_byteorder = subproject('byteorder')
lib_byteorder = sub_byteorder.get_variable('lib')

sub_crc16 = subproject('rust-crc16')
lib_crc16 = sub_crc16.get_variable('lib')

if get_option('afrl_internal')
  subdir('UxAS-afrl_internal')
endif

# https://github.com/zeromq/{zeromq, czmq, cppzmq, zyre}
sub_zeromq              = subproject('zeromq')
lib_zeromq              = sub_zeromq.get_variable('lib')

sub_czmq                = subproject('czmq')
lib_czmq                = sub_czmq.get_variable('lib')

sub_cppzmq              = subproject('cppzmq')
lib_cppzmq              = sub_cppzmq.get_variable('lib')

sub_zyre                = subproject('zyre')
lib_zyre                = sub_zyre.get_variable('lib')

# Windows-only:
# https://github.com/jedisct1/libsodium

# https://www.sqlite.org/src
sub_sqlite3             = subproject('sqlite3')
lib_sqlite3             = sub_sqlite3.get_variable('lib')

# https://github.com/SRombauts/SQLiteCpp
sub_sqlitecpp           = subproject('sqlitecpp')
lib_sqlitecpp           = sub_sqlitecpp.get_variable('lib')

# https://github.com/madler/zlib
sub_zlib                = subproject('zlib')
lib_zlib                = sub_zlib.get_variable('lib')

# https://github.com/nmoinvaz/minizip
sub_minizip             = subproject('minizip')
lib_minizip             = sub_minizip.get_variable('lib')

dep_boost = dependency(
  'boost',
  modules: ['filesystem', 'regex', 'system'],
  static: true,
  fallback: ['boost', 'dep_boost'],
)

# https://github.com/mikalhart/TinyGPS
# The TinyGPS repo captured by UxAS does not seem to be available.
# The repo contains *only* version 13, while UxAS uses what appears
# to be version 12. Perhaps contact the author...?
sub_tinygps             = subproject('TinyGPS')
lib_tinygps             = sub_tinygps.get_variable('lib')

# https://github.com/wjwwood/serial
sub_serial              = subproject('serial')
lib_serial              = sub_serial.get_variable('lib')

# https://github.com/zeux/pugixml
# No versions of this pugixml repo are compatible.
sub_pugixml             = subproject('PugiXML')
lib_pugixml             = sub_pugixml.get_variable('lib')

subdir('src/DPSS')

subdir('src/VisilibityLib')

if not get_option('afrl_internal')
  subdir('src/LMCP')
  subdir('src/LMCP/rs')
endif

subdir('src/Communications')

subdir('src/Tasks')

subdir('src/Services')

subdir('src/Utilities')

subdir('src/Plans')

dep_thread              = dependency('threads')

libs = [
  lib_services,
  lib_tasks,
  lib_lmcp,
  lib_uxas_communications,
  lib_zeromq,
  lib_zyre,
  lib_czmq,
  lib_cppzmq,
  lib_utilities,
  lib_sqlitecpp,
  lib_sqlite3,
  lib_pugixml,
  lib_visilibity,
  lib_serial,
  lib_plans,
  lib_tinygps,
  lib_minizip,
  lib_zlib,
  lib_dpss,
]

if get_option('afrl_internal')
  libs += libs_internal
endif

# creates src/Includes/config.h
subdir('src/Includes')

deps = []

# OpenGL, specifically the GLU library
deps += [dependency('gl')]
if os == 'darwin'
  # newer MacOS splits out GLU into a separate framework, but we can't
  # ask Meson for the version in order to handle things differently
  deps += [dependency('glu', required: false)]
  glu_functions = ['gluNewTess', 'gluDeleteTess', 'gluErrorString']
  foreach fn : glu_functions
    if not cpp.has_function(fn, dependencies: deps)
      error('GLU library functions not found')
    endif
  endforeach
elif os.startswith('linux')
  deps += [dependency('glu')]
elif os == 'windows'
  deps += [cpp.find_library('glu32')]
endif

deps += [
  dep_thread,
  dep_boost,
]

if get_option('afrl_internal')
  deps += deps_internal
endif

cpp_args = []
if cpp.get_id() == 'msvc'
  cpp_args += ['/std:c++14']
else
  cpp_args += ['-std=c++11']
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
      '3rd/cppzmq-4.2.2',
      '3rd/zeromq-4.2.3/include',
      '3rd/PugiXML/src',
      '3rd/sqlite-amalgamation-3120200',
      '3rd/SQLiteCpp-1.3.1/include',
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

