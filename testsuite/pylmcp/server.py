"""Implement a server that can send/receive uxas message."""
from queue import Queue
from pylmcp.message import Message
from pylmcp import Object
from pylmcp.uxas import UxAS, PublishPullBridge, SubscribePushBridge, AutomationRequestValidator, UxASConfig
import threading
import time
import typing
import zmq
import os

DEFAULT_IN_URL=os.environ.get('IN_SERVER_URL', 'tcp://127.0.0.1:5560')
DEFAULT_OUT_URL=os.environ.get('OUT_SERVER_URL', 'tcp://127.0.0.1:5561')

class ServerTimeout(Exception):
    pass


class Server(object):
    """Handle messages from UxAS bus.

    Example::

        with Server() as s:
            m = s.read_msg()
            s.send_msg(m)
    """

    def __init__(self,
                 out_url: str = DEFAULT_IN_URL,
                 in_url: str = DEFAULT_OUT_URL,
                 bridge_service: bool = True,
                 bridge_cfg: typing.Union[None, UxASConfig] = None,
                 entity_id: int = 100):
        """Start a server that listen for UxAS messages.

        :param out_url: url on which messages can be sent
        :type out_url: str
        :param in_url: url on which the server listen
        :type in_url: str
        :param bridge_service: if True start an uxas with the
            PubPull bridge set
        :type bridge_service: bool
        :param bridge_cfg: if not None, use that as base
            configuration for the bridge
        :type bridge_cfg: pylmcp.uxas.UxASConfig
        :param entity_id: entity id
        :type entity_id: int
        """
        self.out_url = out_url
        self.in_url = in_url
        self.ctx = zmq.Context()
        self.entity_id = entity_id

        # Set incoming messages socket (subscribe to all messages)
        self.in_socket = self.ctx.socket(zmq.SUB)
        self.in_socket.connect(self.in_url)
        self.in_socket.setsockopt(zmq.SUBSCRIBE, b"")

        # Set socket to send messages
        self.out_socket = self.ctx.socket(zmq.PUSH)
        self.out_socket.connect(self.out_url)

        # Thread that read UxAS message in background
        self.listen_task = None

        # Internal queue holding all zeromq received messages
        self.in_msg_queue = Queue() # type: Queue

        # Setting stop_listening to True will cause the thread in
        # charge of listening for incoming messages to stop
        self.stop_listening = False

        self.bridge = None # type: typing.Union[UxAS, None]

        if bridge_service:
            self.bridge = UxAS(self.entity_id)
            if bridge_cfg is not None:
                self.bridge.cfg = bridge_cfg
            self.bridge.cfg += PublishPullBridge(
                pub_address=self.in_url,
                pull_address=self.out_url)
            # self.bridge.cfg += AutomationRequestValidator()
            self.bridge.run()
            # Needed ???
            time.sleep(0.2)

        # Start the listening thread
        self.start_listening()

    def stop(self):
        """Stop listening for new messages."""
        self.stop_listening = True
        if self.bridge is not None:
            self.bridge.interrupt()

    def get_uxas(self, **kwargs):
        """Get an uxas instance.

        The instance has at least the SubscribePushBridge service enabled.

        :param kwargs: arguments are passed to the UxAS initialize function.
        :type kwargs: dict
        """
        result = UxAS(entity_id=self.entity_id, **kwargs)
        result.cfg += SubscribePushBridge(
            sub_address=self.in_url,
            push_address=self.out_url)
        return result

    def __del__(self):
        # Ensure that we don't block on termination
        self.stop()

    def has_msg(self):
        """Check for new messages.

        :return: True if they are messages in the queue.
        :rtype: bool
        """
        return not self.in_msg_queue.empty()

    def read_msg(self):
        """Read a message from the queue.

        This call is blocking so ensure to call has_msg before to check
        for message availability.

        :return: a decoded UxAS message
        :rtype: pylmcp.message.Message
        """
        return Message.unpack(self.in_msg_queue.get())

    def send_msg(self, msg):
        """Send an UxAS message.

        :param msg: a UxAS message or an LMCP Object. When an object is
            given, a message is create automatically with the bridge
            entity_id and a service_id set to 0
        :type msg: pylmcp.message.Message | pylmcp.Object
        """
        if isinstance(msg, Object):
            m = Message(obj=msg,
                        source_entity_id=self.bridge.cfg.entity_id,
                        source_service_id=0)
        else:
            m = msg

        return self.out_socket.send(m.pack())

    def __enter__(self):
        return self

    def __exit__(self, _type, _value, _tb):
        self.stop()

    def wait_for_msg(self, descriptor=None, timeout=10.0):
        """Wait for a message.

        :param descriptor: if not None wait for a specific message that match
            the descriptor name
        :type descriptor: str
        :param timeout: timeout in s
        :type timeout: float | int
        """
        start_time = time.time()
        current_time = start_time
        msg = None

        while current_time - start_time < timeout:
            if self.has_msg():
                msg = self.read_msg()
                if descriptor is None or msg.descriptor == descriptor:
                    break
                else:
                    msg = None
            time.sleep(0.2)
            current_time = time.time()

        if msg is None:
            raise ServerTimeout

        return msg

    def start_listening(self):
        """Starts a thread listening for incoming messages.

        This function is called on Server initialization
        """
        def listen():
            poller = zmq.Poller()
            poller.register(self.in_socket, zmq.POLLIN)

            while not self.stop_listening:
                ready_sockets = poller.poll(timeout=1000)
                if ready_sockets:
                    for socket in ready_sockets:
                        raw_msg = socket[0].recv(0, True, False)
                        self.in_msg_queue.put(raw_msg)

        self.listen_task = threading.Thread(target=listen,
                                            name='uxas-listen')
        self.listen_task.daemon = True
        self.listen_task.start()
