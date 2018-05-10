project('zeromq', 'cpp')

os = target_machine.system()
cpp = meson.get_compiler('cpp')
cpp_args = ['-DHAVE_CXX11=1']
deps = []
cdata = configuration_data()

if os == 'linux'
  cpp_args += ['-DLINUX', '-DZMQ_HAVE_LINUX=1']
  if cpp.get_id() == 'g++'
    cpp_args += ['-D_GNU_SOURCE']
  endif
elif os == 'darwin'
  cpp_args += ['-D_DARWIN_C_SOURCE', '-DZMQ_HAVE_OSX=1']
elif os == 'windows'
  cpp_args += [
    '-D_CRT_SECURE_NO_WARNINGS',
	'-D_WINSOCK_DEPRECATED_NO_WARNINGS',
	'-DFD_SETSIZE=16384',
	'-DWIN32_LEAN_AND_MEAN',
	'-DZMQ_USE_SELECT',
	'-DZMQ_STATIC',
	'-DZMQ_HAVE_WINDOWS=1',
  ]
  deps += [
    cpp.find_library('Advapi32'),
	cpp.find_library('Ws2_32'),
	cpp.find_library('Rpcrt4'),
	cpp.find_library('Iphlpapi'),
  ]
endif

check_headers = [
  ['HAVE_ALLOCA_H', 'alloca.h'],
  ['HAVE_ARPA_INET_H', 'arpa/inet.h'],
  ['HAVE_DLFCN_H', 'dlfcn.h'],
  ['HAVE_ERRNO_H', 'errno.h'],
  ['HAVE_GSSAPI_GSSAPI_GENERIC_H', 'gssapi/gssapi_generic.h'],
  ['HAVE_IFADDRS_H', 'ifaddrs.h'],
  ['HAVE_INTTYPES_H', 'inttypes.h'],
  ['HAVE_LIMITS_H', 'limits.h'],
  ['HAVE_MEMORY_H', 'memory.h'],
  ['HAVE_NETINET_IN_H', 'netinet/in.h'],
  ['HAVE_NETINET_TCP_H', 'netinet/tcp.h'],
  ['HAVE_STDBOOL_H', 'stdbool.h'],
  ['HAVE_STDDEF_H', 'stddef.h'],
  ['HAVE_STDINT_H', 'stdint.h'],
  ['HAVE_STDLIB_H', 'stdlib.h'],
  ['HAVE_STRINGS_H', 'strings.h'],
  ['HAVE_STRING_H', 'string.h'],
  ['HAVE_SYS_EVENTFD_H', 'sys/eventfd.h'],
  ['HAVE_SYS_SOCKET_H', 'sys/socket.h'],
  ['HAVE_SYS_STAT_H', 'sys/stat.h'],
  ['HAVE_SYS_TIME_H', 'sys/time.h'],
  ['HAVE_SYS_TYPES_H', 'sys/types.h'],
  ['HAVE_SYS_UIO_H', 'sys/uio.h'],
  ['HAVE_TIME_H', 'time.h'],
  ['HAVE_UNISTD_H', 'unistd.h'],
  ['HAVE_WINDOWS_H', 'windows.h'],
]

foreach h : check_headers
  if cpp.has_header(h.get(1))
    cdata.set(h.get(0), 1)
    if h.get(0) == 'HAVE_SYS_EVENTFD_H'
      cpp_args += ['-DZMQ_HAVE_EVENTFD']
    endif

    if h.get(0) == 'HAVE_IFADDRS_H'
      cpp_args += ['-DZMQ_HAVE_IFADDRS']
    endif

  endif
endforeach

# some headers define additional flags
if cpp.has_header('sys/uio.h')
  cpp_args += ['-DZMQ_HAVE_UIO']
endif

# check for both time and sys/time
if cpp.has_header('time.h') and cpp.has_header('sys/time.h')
  cpp_args += ['-DTIME_WITH_SYS_TIME']
endif

check_functions = [
  ['HAVE_ACCEPT4', 'accept4', '#include <sys/socket.h>'],
  ['HAVE_CLOCK_GETTIME', 'clock_gettime', '#include<time.h>'],
# check token ('HAVE_DECL_LOCAL_PEERCRED',)
# check token ('HAVE_DECL_SO_PEERCRED',)
  ['HAVE_FORK', 'fork', '#include<unistd.h>'],
  ['HAVE_FREEIFADDRS', 'freeifaddrs', '#include <ifaddrs.h>'],
  ['HAVE_GETHRTIME', 'gethrtime', '#include <sys/time.h>'],
  ['HAVE_GETIFADDRS', 'getifaddrs', '#include <ifaddrs.h>'],
  ['HAVE_GETTIMEOFDAY', 'gettimeofday', '#include<sys/time.h>'],
  ['HAVE_LIBGSSAPI_KRB5', 'gss_init_sec_context', '#include <gssapi/gssapi.h>'],
# check token ('HAVE_LIBIPHLPAPI',)
# check token ('HAVE_LIBNSL',)
# check token ('HAVE_LIBPTHREAD',)
# check token ('HAVE_LIBRPCRT4',)
# check token ('HAVE_LIBRT',)
# check token ('HAVE_LIBSOCKET',)
# check token ('HAVE_LIBWS2_32',)
  ['HAVE_MEMSET', 'memset', '#include<string.h>'],
  ['HAVE_POSIX_MEMALIGN', 'posix_memalign', '#include <stdlib.h>'],
  ['HAVE_PERROR', 'perror', '#include <errno.h>'],
  ['HAVE_SOCKET', 'socket', '#include<sys/socket.h>'],
# check token ('HAVE__BOOL',)
]

# Determine polling system

kqueue = '''
#include <sys/types.h>
#include <sys/event.h>
#include <sys/time.h>

int main() {
struct kevent t_kev;
kqueue();
}
'''

epoll = '''
#include <sys/epoll.h>

int main() {
struct epoll_event t_ev;
int r;
r = epoll_create(10);
return(r < 0);
}
'''

devpoll = '''
#include <sys/devpoll.h>

int main() {
struct pollfd t_devpoll;
int fd = open("/dev/poll", O_RDWR);
}
'''

poll = '''
#include <poll.h>

int main() {
struct pollfd t_poll;
poll(&t_poll, 1, 1);
}
'''

select = '''
#ifdef ZMQ_HAVE_WINDOWS
#include "winsock2.h"
#elif defined ZMQ_HAVE_OPENVMS
#include <sys/types.h>
#include <sys/time.h>
#else
#include <sys/select.h>
#endif

int main() {
fd_set t_rfds;
struct timeval tv;

FD_ZERO(&t_rfds);
FD_SET(0, &t_rfds);

tv.tv_sec = 5;
tv.tv_usec = 0;

select(1, &t_rfds, NULL, NULL, &tv);
}
'''

if cpp.links(kqueue, name: 'kqueue links')
  cpp_args += ['-DZMQ_USE_KQUEUE']
elif meson.is_cross_build() and cpp.links(epoll, name: 'epoll links')
  cpp_args += ['-DZMQ_USE_EPOLL']
elif not meson.is_cross_build() and cpp.run(epoll, name: 'epoll runs').returncode() == 0
  cpp_args += ['-DZMQ_USE_EPOLL']
elif cpp.links(devpoll, name: 'devpoll links')
  cpp_args += ['-DZMQ_USE_DEVPOLL']
elif cpp.links(poll, name: 'poll links')
  cpp_args += ['-DZMQ_USE_POLL']
elif cpp.links(select, name: 'select links')
  cpp_args += ['-DZMQ_USE_SELECT']
endif

foreach f : check_functions
  if cpp.has_function(f.get(1), prefix : f.get(2))
    cdata.set(f.get(0), 1)
  endif
endforeach

dep_libsodium = dependency('libsodium', required: false)
if dep_libsodium.found()
  cdata.set('HAVE_LIBSODIUM', 1)
  deps += [dep_libsodium]
endif

if cpp.has_header_symbol('stdbool.h', '_Bool')
  cdata.set('HAVE__BOOL', 1)
endif

deps += [dependency('threads')]

subdir('src')

lib = static_library(
  'zeromq',
  [
    'src/address.cpp',
    'src/client.cpp',
    'src/clock.cpp',
    'src/ctx.cpp',
    'src/curve_client.cpp',
    'src/curve_mechanism_base.cpp',
    'src/curve_server.cpp',
    'src/dealer.cpp',
    'src/decoder_allocators.cpp',
    'src/devpoll.cpp',
    'src/dgram.cpp',
    'src/dish.cpp',
    'src/dist.cpp',
    'src/epoll.cpp',
    'src/err.cpp',
    'src/fq.cpp',
    'src/gather.cpp',
    'src/gssapi_client.cpp',
    'src/gssapi_mechanism_base.cpp',
    'src/gssapi_server.cpp',
    'src/io_object.cpp',
    'src/io_thread.cpp',
    'src/ip.cpp',
    'src/ipc_address.cpp',
    'src/ipc_connecter.cpp',
    'src/ipc_listener.cpp',
    'src/kqueue.cpp',
    'src/lb.cpp',
    'src/mailbox.cpp',
    'src/mailbox_safe.cpp',
    'src/mechanism.cpp',
    'src/mechanism_base.cpp',
    'src/metadata.cpp',
    'src/msg.cpp',
    'src/mtrie.cpp',
    'src/norm_engine.cpp',
    'src/null_mechanism.cpp',
    'src/object.cpp',
    'src/options.cpp',
    'src/own.cpp',
    'src/pair.cpp',
    'src/pgm_receiver.cpp',
    'src/pgm_sender.cpp',
    'src/pgm_socket.cpp',
    'src/pipe.cpp',
    'src/plain_client.cpp',
    'src/plain_server.cpp',
    'src/poll.cpp',
    'src/poller_base.cpp',
    'src/pollset.cpp',
    'src/precompiled.cpp',
    'src/proxy.cpp',
    'src/pub.cpp',
    'src/pull.cpp',
    'src/push.cpp',
    'src/radio.cpp',
    'src/random.cpp',
    'src/raw_decoder.cpp',
    'src/raw_encoder.cpp',
    'src/reaper.cpp',
    'src/rep.cpp',
    'src/req.cpp',
    'src/router.cpp',
    'src/scatter.cpp',
    'src/select.cpp',
    'src/server.cpp',
    'src/session_base.cpp',
    'src/signaler.cpp',
    'src/socket_base.cpp',
    'src/socket_poller.cpp',
    'src/socks.cpp',
    'src/socks_connecter.cpp',
    'src/stream.cpp',
    'src/stream_engine.cpp',
    'src/sub.cpp',
    'src/tcp.cpp',
    'src/tcp_address.cpp',
    'src/tcp_connecter.cpp',
    'src/tcp_listener.cpp',
    'src/thread.cpp',
    'src/timers.cpp',
    'src/tipc_address.cpp',
    'src/tipc_connecter.cpp',
    'src/tipc_listener.cpp',
    'src/trie.cpp',
    'src/udp_address.cpp',
    'src/udp_engine.cpp',
    'src/v1_decoder.cpp',
    'src/v1_encoder.cpp',
    'src/v2_decoder.cpp',
    'src/v2_encoder.cpp',
    'src/vmci.cpp',
    'src/vmci_address.cpp',
    'src/vmci_connecter.cpp',
    'src/vmci_listener.cpp',
    'src/xpub.cpp',
    'src/xsub.cpp',
    'src/zap_client.cpp',
    'src/zmq.cpp',
    'src/zmq_utils.cpp',
  ],
  dependencies: deps,
  cpp_args: cpp_args,
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
