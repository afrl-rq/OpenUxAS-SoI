from pylmcp import Object

class Message(object):
    def __init__(self, obj):
        self.obj = obj
        self.address = obj.object_class.full_name
        self.descriptor = obj.object_class.full_name
        self.content_type = 'lmcp'
        self.source_group = ''
        self.source_entity_id = 300
        self.source_service_id = 51

    @classmethod
    def read(self, socket):
        raw_msg = socket.recv(0, True, False)

        address, attributes, payload= raw_msg.split('$', 2)
        content_type, descriptor, source_group, \
            source_entity_id, source_service_id = \
            attributes.split('|', 4)
        print address
        print len(source_group)
        print source_entity_id
        print source_service_id
        obj = Object.unpack(data=payload)
        return None
        # return Message(obj)
        

    def send(self, socket):
        payload = self.obj.pack()
        attributes = "|".join([self.content_type,
                               self.descriptor,
                               self.source_group,
                               str(self.source_entity_id),
                               str(self.source_service_id)])
        raw_msg = "$".join([self.address, attributes, payload])
        socket.send(raw_msg)

