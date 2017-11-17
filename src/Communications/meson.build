cpp_args = []
cpp = meson.get_compiler('cpp')

if cpp.get_id() == 'msvc'
  cpp_args += [
    '/std:c++14',
    '-DZMQ_DEFINED_STDINT',
    '-DZMQ_STATIC',
    '-DLIBCZMQ_STATIC',
    '-DLIBZYRE_STATIC',
  ]
else
  cpp_args += [
    '-std=c++11',
    '-Wno-unused-function',
    '-Wno-unused-variable',
  ]
endif

inc_3rd = include_directories('.')
if get_option('internal_3rd_libraries')
  inc_3rd = include_directories(
      '../../3rd/cppzmq-4.2.1',
      '../../3rd/czmq-3.0.1/include',
      '../../3rd/zeromq-4.1.6/include',
      '../../3rd/zyre-1.1.0/include',
      '../../3rd/sqlite-amalgamation-3120200',
      '../../3rd/SQLiteCpp-1.3.1/include',
    )
endif

inc_dirs = [
    include_directories(
      '../../src/Includes',
      '../../src/Utilities',
      '../../src/Services',
      '../../3rd/PugiXML/src',
      '../../3rd/serial-1.2.1/include',
    ),
    inc_3rd,
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
  cpp_args: cpp_args,
  include_directories:inc_dirs, 
)
