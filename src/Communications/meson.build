cpp_args_comms = cpp_args

if cpp.get_id() == 'msvc'
  cpp_args_comms += [
    '-DZMQ_STATIC',
    '-DCZMQ_STATIC',
    '-DZYRE_STATIC',
    '-DLIBZMQ_STATIC',
    '-DLIBCZMQ_STATIC',
    '-DLIBZYRE_STATIC',
  ]
else
  cpp_args_comms += [
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ]
endif

inc_dirs = [
  include_directories(
    '../../src/Includes',
    '../../src/Utilities',
    '../../src/Services',
  ),
  incs_lmcp,
]

lib_uxas_communications = static_library(
  'uxas_messages',
  [
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
  cpp_args: cpp_args_comms,
  dependencies: [
    dep_czmq,
    dep_cppzmq,
    dep_pugixml,
    dep_serial,
    dep_zeromq,
    dep_zyre,
  ],
  include_directories: inc_dirs,
)
