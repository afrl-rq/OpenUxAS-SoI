project('zyre', 'c')

os = target_machine.system()
c = meson.get_compiler('c')
c_args = []
cdata = configuration_data()

dep_zeromq = dependency(
  'libzmq',
  fallback: ['zeromq', 'dep'],
)

dep_czmq = dependency(
  'libczmq',
  fallback: ['czmq', 'dep'],
)

deps = [
  dep_zeromq,
  dep_czmq,
]

if os == 'linux'
  c_args += [
    '-std=c11',
    '-DLINUX',
    '-D_GNU_SOURCE',
    '-DZYRE_HAVE_LINUX=1',
  ]
elif os == 'darwin'
  c_args += [
    '-std=c11',
    '-D_DARWIN_C_SOURCE',
    '-DZYRE_HAVE_OSX=1',
  ]
elif os == 'windows'
  c_args += [
    '-D_CRT_SECURE_NO_WARNINGS',
    '-DBASE_THREADSAFE',
    '-DZYRE_STATIC',
    '-DZYRE_HAVE_WINDOWS=1',
    '-DZMQ_USE_SELECT',
    '-DZMQ_STATIC',
    '-DLIBZMQ_STATIC',
    '-DZMQ_HAVE_WINDOWS=1',
    '-DCZMQ_STATIC',
    '-DLIBCZMQ_STATIC',
  ]
  deps += [
    c.find_library('Ws2_32'),
    c.find_library('Rpcrt4'),
    c.find_library('Iphlpapi'),
  ]
endif

check_headers = [
  ['HAVE_ARPA_INET_H', 'arpa/inet.h'],
  ['HAVE_DLFCN_H', 'dlfcn.h'],
  ['HAVE_ERRNO_H', 'errno.h'],
  ['HAVE_IFADDRS_H', 'ifaddrs.h'],
  ['HAVE_INTTYPES_H', 'inttypes.h'],
  ['HAVE_LIMITS_H', 'limits.h'],
  ['HAVE_LINUX_WIRELESS_H', 'linux/wireless.h'],
  ['HAVE_MEMORY_H', 'memory.h'],
  ['HAVE_NETINET_IN_H', 'netinet/in.h'],
  ['HAVE_NETINET_TCP_H', 'netinet/tcp.h'],
  ['HAVE_NET_IF_H', 'net/if.h'],
  ['HAVE_NET_IF_MEDIA_H', 'net/if_media.hh'],
  ['HAVE_STDBOOL_H', 'stdbool.h'],
  ['HAVE_STDDEF_H', 'stddef.h'],
  ['HAVE_STDINT_H', 'stdint.h'],
  ['HAVE_STDLIB_H', 'stdlib.h'],
  ['HAVE_STRINGS_H', 'strings.h'],
  ['HAVE_STRING_H', 'string.h'],
  ['HAVE_SYS_SOCKET_H', 'sys/socket.h'],
  ['HAVE_SYS_STAT_H', 'sys/stat.h'],
  ['HAVE_SYS_TIME_H', 'sys/time.h'],
  ['HAVE_SYS_TYPES_H', 'sys/types.h'],
  ['HAVE_TIME_H', 'time.h'],
  ['HAVE_UNISTD_H', 'unistd.h'],
  ['HAVE_WINDOWS_H', 'windows.h'],
]

foreach h : check_headers
  if c.has_header(h.get(1))
    cdata.set(h.get(0), 1)
  endif
endforeach

# check for both time and sys/time
if c.has_header('time.h') and c.has_header('sys/time.h')
  c_args += ['-DTIME_WITH_SYS_TIME']
endif

check_functions = [
  ['HAVE_CLOCK_GETTIME', 'clock_gettime', '#include<time.h>'],
  ['HAVE_GETIFADDRS', 'getifaddrs', '#include <ifaddrs.h>'],
  ['HAVE_GETTIMEOFDAY', 'gettimeofday', '#include<sys/time.h>'],
  ['HAVE_MEMSET', 'memset', '#include<string.h>'],
  ['HAVE_PERROR', 'perror', '#include <errno.h>'],
  ['HAVE_SOCKET', 'socket', '#include<sys/socket.h>'],
]

foreach f : check_functions
  if c.has_function(f.get(1), prefix : f.get(2))
    cdata.set(f.get(0), 1)
  endif
endforeach

if c.has_header_symbol('stdbool.h', '_Bool')
  cdata.set('HAVE__BOOL', 1)
endif

# check for libsodium dependency
dep_libsodium = dependency('libsodium', required: false)
if dep_libsodium.found()
  cdata.set('HAVE_LIBSODIUM', 1)
  deps += [dep_libsodium]
endif
deps += [dependency('threads')]

subdir('src')

lib = static_library(
  'zyre',
  [
    'src/zpinger.c',
    'src/zre_msg.c',
    'src/zyre.c',
    'src/zyre_event.c',
    'src/zyre_group.c',
    'src/zyre_node.c',
    'src/zyre_peer.c',
  ],
  dependencies: deps,
  c_args: c_args,
  include_directories: include_directories(
    'include',
    'src',
  ),
)

dep = declare_dependency(
  link_with: lib,
  include_directories: include_directories(
    'include',
  ),
)
