project('zyre', 'c')

c_args = []

os = target_machine.system()
if os == 'linux'
  c_args += [
    '-std=c11',
  	'-DLINUX',
	'-D_GNU_SOURCE',
  ]
elif os == 'darwin'
  c_args += [
  	'-std=c11',
  ]
elif os == 'windows'
  c_args += [
    '/std=c++14',
	'-DZMQ_STATIC',
	'-DLIBCZMQ_STATIC',
  	'-DLIBZYRE_STATIC',
  ]
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
	c_args: c_args,
	include_directories: include_directories(
		'../czmq-3.0.1/include',
		'../zeromq-4.1.6/include',
	),
)
