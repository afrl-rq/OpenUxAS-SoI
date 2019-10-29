"""Implement a server that can send/receive uxas message."""
from Queue import Queue
from pylmcp.message import Message
import threading
import zmq


class Server(object):
    """Handle messages from UxAS bus.

    Example::

        with Server() as s:
            m = s.read_msg()
            s.send_msg(m)
    """

    def __init__(self,
                 out_url="tcp://127.0.0.1:5561",
                 in_url="tcp://127.0.0.1:5560"):
        """Start a server that listen for UxAS messages.

        :param out_url: url on which messages can be sent
        :type out_url: str
        :param in_url: url on which the server listen
        :type in_url: str
        """
        self.out_url = out_url
        self.in_url = in_url
        self.ctx = zmq.Context()

        # Set incoming messages socket (subscribe to all messages)
        self.in_socket = self.ctx.socket(zmq.SUB)
        self.in_socket.connect(self.in_url)
        self.in_socket.setsockopt(zmq.SUBSCRIBE, "")

        # Set socket to send messages
        self.out_socket = self.ctx.socket(zmq.PUSH)
        self.out_socket.connect(self.out_url)

        # Thread that read UxAS message in background
        self.listen_task = None

        # Internal queue holding all zeromq received messages
        self.in_msg_queue = Queue()

        # Setting stop_listening to True will cause the thread in
        # charge of listening for incoming messages to stop
        self.stop_listening = False

        # Start the listening thread
        self.start_listening()

    def stop(self):
        """Stop listening for new messages."""
        self.stop_listening = True

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

        :param msg: a UxAS message
        :type msg: pylmcp.message.Message
        """
        self.out_socket.send(msg.pack())

    def __enter__(self):
        return self

    def __exit__(self, _type, _value, _tb):
        self.stop()

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
