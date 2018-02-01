project('czmq', 'c')

dep_zeromq = dependency(
  'libzmq',
  fallback: ['zeromq', 'dep'],
)

cc = meson.get_compiler('c')

cdata = configuration_data()
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
  ['HAVE_NET_IF_MEDIA_H', 'net/if/media.h'],
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
  ['HAVE_UNISTD_H', 'unistd.h'],
  ['HAVE_WINDOWS_H', 'windows.h'],
]

foreach h : check_headers
  if cc.has_header(h.get(1))
    cdata.set(h.get(0), 1)
  endif
endforeach

# some headers define additional flags
if cc.has_header_symbol('stdbool.h', '_Bool')
  cdata.set('HAVE__BOOL', 1)
endif

check_functions = [
  ['HAVE_GETIFADDRS', 'getifaddrs', '#include <ifaddrs.h>'],
  ['HAVE_GETTIMEOFDAY', 'gettimeofday', '#include<sys/time.h>'],
  ['HAVE_MEMSET', 'memset', '#include<string.h>'],
]

foreach f : check_functions
  if cc.has_function(f.get(1), prefix : f.get(2))
    cdata.set(f.get(0), 1)
  endif
endforeach

c = meson.get_compiler('c')
c_args = []
deps = [
  dep_zeromq,
]

os = target_machine.system()
if os == 'linux'
  c_args += ['-std=c11', '-D_GNU_SOURCE', '-DLINUX', '-DCZMQ_HAVE_LINUX=1']
elif os == 'darwin'
  c_args += ['-std=c11', '-D_DARWIN_C_SOURCE', '-DCZMQ_HAVE_OSX=1']
elif os == 'windows'
  c_args += [
    '-D_CRT_SECURE_NO_WARNINGS',
    '-DBASE_THREADSAFE',
    '-DCZMQ_STATIC',
    '-DZMQ_USE_SELECT',
    '-DZMQ_STATIC',
    '-DLIBZMQ_STATIC',
    '-DZMQ_HAVE_WINDOWS=1',
  ]
  cdata.set('CZMQ_HAVE_WINDOWS', 1)
  cdata.set('HAVE_LIBUUID', 1)
  deps += [
    c.find_library('Rpcrt4'),
    c.find_library('Iphlpapi'),
    c.find_library('WS2_32'),
  ]
endif

subdir('src')

lib = static_library(
  'czmq',
  [
    'foreign/sha1/sha1.c',
    'foreign/slre/slre.c',
    'src/zactor.c',
    'src/zarmour.c',
    'src/zauth.c',
    'src/zbeacon.c',
    'src/zcert.c',
    'src/zcertstore.c',
    'src/zchunk.c',
    'src/zclock.c',
    'src/zconfig.c',
    'src/zdigest.c',
    'src/zdir.c',
    'src/zdir_patch.c',
    'src/zfile.c',
    'src/zframe.c',
    'src/zgossip.c',
    'src/zgossip_msg.c',
    'src/zhash.c',
    'src/zhashx.c',
    'src/ziflist.c',
    'src/zlist.c',
    'src/zlistx.c',
    'src/zloop.c',
    'src/zmonitor.c',
    'src/zmsg.c',
    'src/zpoller.c',
    'src/zproc.c',
    'src/zproxy.c',
    'src/zrex.c',
    'src/zsock.c',
    'src/zstr.c',
    'src/zsys.c',
    'src/zuuid.c',
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
