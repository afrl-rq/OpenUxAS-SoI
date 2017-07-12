import zmq, json, string, sys
sys.path.insert(0, '../../../src/LMCP/py')
from lmcp import LMCPFactory

if __name__ == '__main__':

    # prepare LMCP factory
    factory = LMCPFactory.LMCPFactory();

    # Socket to talk to server
    context = zmq.Context()
    socket_sub = context.socket(zmq.SUB)
    socket_sub.connect("tcp://127.0.0.1:5560")

    # subscribe to all possible messages
    # duplicate of UxAS config file, but necessary
    for c in string.ascii_letters:
        socket_sub.setsockopt(zmq.SUBSCRIBE, c)

    socket_send = context.socket(zmq.PUSH)
    socket_send.connect("tcp://127.0.0.1:5561")

    # main loop: receive a message, then process it
    while True:
        data = socket_sub.recv()
        # messages are single part with a header followed by
        # serialized LMCP
        # header format: [address]$[format]|[type]|[group]|[entity]|[service]$
        address, attributes, msg = data.split('$', 2)
        msg_format, msg_type, msg_group, entityid, serviceid = attributes.split('|',4)
        obj = factory.getObject(msg)
        
        # sending as entityid{0} and serviceid{0}, so check for loopback
        # CreateServiceMessage currently has xml parsing problems, so remove
        if (int(entityid) == 0 and int(serviceid) == 0) or obj.FULL_LMCP_TYPE_NAME == "uxas.messages.uxnative.CreateNewService":
            continue

        print("Received: " + obj.FULL_LMCP_TYPE_NAME)

        # convert to XML
        xmlStr = obj.toXMLStr("")
        
        # convert from XML
        obj = factory.unpackFromXMLString(xmlStr)[0]
                
        # convert to JSON
        d = obj.toDict()
        j = json.dumps(d)

	    # convert from JSON
        d = json.loads(j)
        obj = factory.unpackFromDict(d)
        
        # syntax to create an object from scratch
        obj = factory.createObjectByName("CMASI", "KeyValuePair")
        obj.set_Key("Hello")
        obj.set_Value("World")
        
        # syntax to send back to UxAS
        header = str(obj.FULL_LMCP_TYPE_NAME) + "$lmcp|" + str(obj.FULL_LMCP_TYPE_NAME) + "||0|0$"
        smsg = LMCPFactory.packMessage(obj, True)
        socket_send.send(header + smsg)
        print("  Sent:   " + obj.FULL_LMCP_TYPE_NAME)

