project('UxAS', 'cpp', subproject_dir: '.')

conf = configuration_data()

link_args = [
  '-ldl',
]

os = target_machine.system()
if os == 'linux'
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
  link_args += ['-lrt']
elif os == 'darwin'
  link_args += ['-framework', 'OpenGL']
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

# https://sourceforge.net/projects/boost/files/boost/1.64.0/boost_1_64_0.zip/download
sub_boostlibs           = subproject('boost')
lib_boostlibs           = sub_boostlibs.get_variable('lib')

# https://github.com/mikalhart/TinyGPS
# The TinyGPS repo captured by UxAS does not seem to be available.
# The repo contains *only* version 13, while UxAS uses what appears
# to be version 12. Perhaps contact the author...?
sub_tinygps             = subproject('3rd/TinyGPS')
lib_tinygps             = sub_tinygps.get_variable('lib')

# https://github.com/wjwwood/serial
sub_serial              = subproject('serial')
lib_serial              = sub_serial.get_variable('lib')

# https://github.com/zeux/pugixml
# No versions of this pugixml repo are compatible.
#sub_pugixml            = subproject('pugixml')
sub_pugixml             = subproject('3rd/PugiXML')
lib_pugixml             = sub_pugixml.get_variable('lib')

sub_plans               = subproject('src/Plans')
lib_plans               = sub_plans.get_variable('lib')

sub_uxas_communications = subproject('src/Communications')
lib_uxas_communications = sub_uxas_communications.get_variable('lib')

sub_dpss                = subproject('src/DPSS')
lib_dpss                = sub_dpss.get_variable('lib')

sub_visilibity          = subproject('src/VisilibityLib')
lib_visilibity          = sub_visilibity.get_variable('lib')

subdir('src/Tasks')

subdir('src/Services')

subdir('src/Utilities')

sub_lmcp                = subproject('src/LMCP')
lib_lmcp                = sub_lmcp.get_variable('lib')

dep_thread              = dependency('threads')
dep_uuid                = dependency('uuid')

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
  lib_boostlibs,
  lib_visilibity,
  lib_serial,
  lib_plans,
  lib_tinygps,
  lib_minizip,
  lib_zlib,
  lib_dpss,
]

# CircumNav, RRTStar
if get_option('afrl_internal')
  conf.set('AFRL_INTERNAL_ENABLED', true)
  # closed-source libraries
  libs += [
    subproject('src/Kestrel').get_variable('lib'),
    subproject('src/Piccolo').get_variable('lib'),
    subproject('3rd/TrilliumSDK').get_variable('lib'),
    subproject('3rd/Tripath').get_variable('lib'),
    subproject('src/UGSManagement').get_variable('lib'),
  ]
endif

# creates src/Includes/config.h
subdir('src/Includes')

deps = [
  dep_thread,
  dep_uuid,
]

if os == 'linux'
  deps += [dependency('glu')]
endif

executable(
  'uxas',
  'src/UxAS_Main.cpp',
  dependencies: deps,
  link_args: link_args,
  cpp_args: [
    '-std=c++11',
  ],
  include_directories: include_directories(
    'src/Utilities',
    'src/LMCP',
    'src/Communications',
    'src/Includes',
    'src/Services',
    'boost_1_64_0',
    'cppzmq-4.2.1',
    'zeromq-4.1.1/include',
    '3rd/PugiXML/src',
    'sqlite-amalgamation-3120200',
    'SQLiteCpp-1.3.1/include',
  ),
  link_with: libs,
)

subdir('tests')
