project('zyre', 'c')

os = target_machine.system()
if os == 'linux'
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

lib = static_library('zyre', [
	'src/perf_local.c',
	'src/perf_remote.c',
	'src/zpinger.c',
	'src/zre_msg.c',
	'src/ztester_beacon.c',
	'src/ztester_gossip.c',
	'src/zyre.c',
	'src/zyre_event.c',
	'src/zyre_group.c',
	'src/zyre_node.c',
	'src/zyre_peer.c',
	'src/zyre_selftest.c',
	],
	cpp_args: [
		'-std=c++11',
		'-DZMQ_USE_EPOLL',
		'-D_GNU_SOURCE',
		'-D_REENTRANT',
		'-D_THREAD_SAFE',
	],
	include_directories: include_directories(
		'../czmq-3.0.1/include',
		'../zeromq-4.1.1/include',
	),
)
