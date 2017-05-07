project('Communications', 'cpp')

os = target_machine.system()
if os == 'linux'
  add_project_arguments('-DLINUX', language: ['c', 'cpp'])
endif

lib = static_library('uxas_messages', [
	'AddressStringMessageReceiverPipe.cpp',
	'AddressStringMessageSenderPipe.cpp',
	'AddressedAttributedMessage.cpp',
	'ImpactSubscribePushBridge.cpp',
	'LmcpObjectMessageReceiverPipe.cpp',
	'LmcpObjectMessageSenderPipe.cpp',
	'LmcpObjectMessageTcpReceiverSenderPipe.cpp',
	'LmcpObjectNetworkBridgeManager.cpp',
	'LmcpObjectNetworkClientBase.cpp',
	'LmcpObjectNetworkPublishPullBridge.cpp',
	'LmcpObjectNetworkSerialBridge.cpp',
	'LmcpObjectNetworkServer.cpp',
	'LmcpObjectNetworkSubscribePushBridge.cpp',
	'LmcpObjectNetworkTcpBridge.cpp',
	'LmcpObjectNetworkZeroMqZyreBridge.cpp',
	'TransportReceiverBase.cpp',
	'ZeroMqAddressStringReceiver.cpp',
	'ZeroMqAddressStringSender.cpp',
	'ZeroMqAddressedAttributedMessageReceiver.cpp',
	'ZeroMqAddressedAttributedMessageSender.cpp',
	'ZeroMqAddressedAttributedMessageTcpReceiverSender.cpp',
	'ZeroMqFabric.cpp',
	'ZeroMqReceiverBase.cpp',
	'ZeroMqSenderBase.cpp',
	'ZeroMqZyreBridge.cpp',
	],
	cpp_args: [
		'-std=c++11',
		'-Wno-unused-function',
		'-Wno-unused-variable',
	],
	include_directories: include_directories(
		'../../src/Includes',
		'../../src/Utilities',
		'../../src/LMCP',
		'../../cppzmq-4.2.1',
		'../../zeromq-4.1.1/include',
		'../../czmq-3.0.1/include',
		'../../zyre-1.1.0/include',
#		'../../pugixml-1.2/src',
		'../../3rd/PugiXML/src',
		'../../serial-1.2.1/include',
	),
)
