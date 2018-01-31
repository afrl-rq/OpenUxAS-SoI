project('UxAS', 'c', 'cpp', subproject_dir: '3rd')

conf = configuration_data()

link_args = []

os = target_machine.system()

if get_option('geo_libs')
    add_project_arguments('-DUSE_GEO_LIBS', language: ['c', 'cpp'])
		link_args += [
      	 '-l:libgdal.a','-l:libGeographic.a','-l:libexpat.a','-l:libz.a']
endif

if os.startswith('linux')
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
	if get_option('internal_3rd_libraries')
    #message('@@@@@ internal_3rd_libraries @@@@@')
		link_args += ['-lrt', '-ldl']
  	else
      message('@@@@@ external_3rd_libraries @@@@@')
  		link_args += [
          '-l:libboost_filesystem.a','-l:libboost_regex.a', '-l:libboost_system.a', 
  				'-l:libzmq.a','-l:libczmq.a','-l:libzyre.a',
          '-l:libSQLiteCpp.a','-l:libsqlite3.a',
          '-l:libgtest.a','-l:libuuid.a',
  				'-lrt', '-ldl']
	endif
elif os == 'darwin'
  link_args += ['-ldl']
elif os == 'windows'
  link_args += []
endif

if get_option('internal_3rd_libraries')
  # https://github.com/zeromq/{zeromq, czmq, cppzmq, zyre}
  sub_zeromq              = subproject('zeromq')
  dep_zeromq              = sub_zeromq.get_variable('dep')

  sub_czmq                = subproject('czmq')
  dep_czmq                = sub_czmq.get_variable('dep')

  sub_cppzmq              = subproject('cppzmq')
  dep_cppzmq              = sub_cppzmq.get_variable('dep')

  sub_zyre                = subproject('zyre')
  dep_zyre                = sub_zyre.get_variable('dep')

  # https://www.sqlite.org/src
  sub_sqlite3             = subproject('sqlite3')
  dep_sqlite3             = sub_sqlite3.get_variable('dep')

  # https://github.com/SRombauts/SQLiteCpp
  sub_sqlitecpp           = subproject('sqlitecpp')
  dep_sqlitecpp           = sub_sqlitecpp.get_variable('dep')

  # https://github.com/madler/zlib
  sub_zlib                = subproject('zlib')
  dep_zlib                = sub_zlib.get_variable('dep')

  # https://github.com/nmoinvaz/minizip
  sub_minizip             = subproject('minizip')
  dep_minizip             = sub_minizip.get_variable('dep')

  dep_boost = dependency(
    'boost',
    modules: ['date-time', 'filesystem', 'regex', 'system'],
    static: true,
    fallback: ['boost', 'dep'],
  )

endif


# https://github.com/mikalhart/TinyGPS
# The TinyGPS repo captured by UxAS does not seem to be available.
# The repo contains *only* version 13, while UxAS uses what appears
# to be version 12. Perhaps contact the author...?
dep_tinygps             = subproject('TinyGPS').get_variable('dep')

# https://github.com/wjwwood/serial
dep_serial              = subproject('serial-1.2.1').get_variable('dep')

# https://github.com/zeux/pugixml
# No versions of this pugixml repo are compatible.
dep_pugixml             = subproject('PugiXML').get_variable('dep')

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

libs = [
  lib_services,
  lib_tasks,
  lib_lmcp,
  lib_uxas_communications,
  lib_utilities,
  lib_visilibity,
  lib_plans,
  lib_dpss,
]

if get_option('afrl_internal')
  libs += libs_internal
endif

# creates src/Includes/config.h
subdir('src/Includes')

# OpenGL, specifically the GLU library
if not (target_machine.cpu_family() == 'arm')
  deps += [dependency('gl')]
endif
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
  if not (target_machine.cpu_family() == 'arm')
    deps += [dependency('glu')]
  endif
elif os == 'windows'
  deps += [cpp.find_library('glu32')]
endif

if get_option('afrl_internal')
  deps += deps_internal
endif

cpp_args = []
if cpp.get_id() == 'msvc'
  cpp_args += ['/std:c++14']
else
  cpp_args += ['-std=c++11']
endif

inc_3rd = include_directories('.')
if get_option('internal_3rd_libraries')
  inc_3rd = include_directories(
  )
endif

#message('@@@@@ link_args [[ @@@@@')
#message(link_args)
#message('@@@@@ ]] link_args @@@@@')


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
    inc_3rd,
    incs_lmcp,
  ],
  link_with: libs,
  install: true,
)

subdir('tests')

if get_option('afrl_internal')
  subdir('UxAS-afrl_internal/tests')
endif
