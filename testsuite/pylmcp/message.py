from pylmcp import Object
from pylmcp.util import Buffer
import json


class Message(object):

    def __init__(self,
                 obj: Object,
                 source_entity_id: int,
                 source_service_id: int,
                 source_group: str = '',
                 content_type: str = 'lmcp',
                 address=None,
                 descriptor=None):
        self.obj = obj
        self.address = obj.object_class.full_name
        self.descriptor = obj.object_class.full_name
        self.content_type = content_type
        self.source_group = source_group
        self.source_entity_id = source_entity_id
        self.source_service_id = source_service_id
        if descriptor is not None:
            self.descriptor = descriptor
        if address is not None:
            self.address = address

    @classmethod
    def unpack(self, raw_msg: bytes) -> "Message":
        """Unpack a received message.

        :param raw_msg: the received message
        :return: a Message object
        """
        # Unpack headers and payload
        address, attributes, payload = raw_msg.split(b'$', 2)
        content_type, descriptor, source_group, \
            source_entity_id, source_service_id = \
            attributes.split(b'|', 4)

        # Unpack the LMCP object
        buf = Buffer(payload)

        # Control character
        buf.unpack("uint32")

        # Size
        buf.unpack("uint32")

        obj = Object.unpack(data=buf)
        assert obj is not None

        return Message(
            obj=obj,
            source_entity_id=int(source_entity_id.decode('utf-8')),
            source_service_id=int(source_service_id.decode('utf-8')),
            source_group=source_group.decode('utf-8'),
            content_type=content_type.decode('utf-8'),
            address=address.decode('utf-8'),
            descriptor=descriptor.decode('utf-8'))

    def pack(self) -> bytes:
        """Create a message that can be sent through the network.

        :return: a string
        :rtype: str
        """
        payload = self.obj.pack()
        attributes = b"|".join([self.content_type.encode('utf-8'),
                                self.descriptor.encode('utf-8'),
                                self.source_group.encode('utf-8'),
                                str(self.source_entity_id).encode('utf-8'),
                                str(self.source_service_id).encode('utf-8')])
        raw_msg = b"$".join([self.address.encode('utf-8'),
                             attributes,
                             payload])
        return raw_msg

    def as_dict(self):
        return {'address': self.address,
                'descriptor': self.descriptor,
                'content_type': self.content_type,
                'source_group': self.source_group,
                'source_entitiy_id': self.source_entity_id,
                'source_service_id': self.source_service_id,
                'obj': self.obj.as_dict()}

    def __str__(self):
        return json.dumps(self.as_dict(), indent=2)
