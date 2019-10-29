from pylmcp import Object
from pylmcp.util import Buffer
import json


class Message(object):

    def __init__(self, obj,
                 source_entity_id,
                 source_service_id,
                 source_group='',
                 content_type='lmcp',
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
    def unpack(self, raw_msg):
        """Unpack a received message.

        :param raw_msg: the received message
        :type raw_msg: str
        :return: a Message object
        :rtype: pylmcp.message.Message
        """
        # Unpack headers and payload
        address, attributes, payload = raw_msg.split('$', 2)
        content_type, descriptor, source_group, \
            source_entity_id, source_service_id = \
            attributes.split('|', 4)

        # Unpack the LMCP object
        buf = Buffer(payload)

        # Control character
        buf.unpack("uint32")

        # Size
        buf.unpack("uint32")

        obj = Object.unpack(data=buf)

        return Message(obj=obj,
                       source_entity_id=source_entity_id,
                       source_service_id=source_service_id,
                       source_group=source_group,
                       content_type=content_type,
                       address=address,
                       descriptor=descriptor)

    def pack(self):
        """Create a message that can be sent through the network.

        :return: a string
        :rtype: str
        """
        payload = self.obj.pack()
        attributes = "|".join([self.content_type,
                               self.descriptor,
                               self.source_group,
                               str(self.source_entity_id),
                               str(self.source_service_id)])
        raw_msg = "$".join([self.address, attributes, payload])
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
