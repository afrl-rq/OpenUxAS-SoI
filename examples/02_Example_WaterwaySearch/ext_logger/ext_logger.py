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
        print("--------------------------------------------")
        
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
        print("obj.toDict(): '%r'\n" % d)
        print("JSON 'dumps' from dict: '%r'\n\n" % j)

	    # convert from JSON
        d2 = json.loads(j)
        obj2 = factory.unpackFromDict(d2)
        print("dict loaded from json: '%r'\n" % d2)
        print("type(obj): %r" % type(obj2))
        print("obj unpacked from dict: '%r'\n\n" % obj2)

        print("d2 same as original d? %r" % (d == d2,))
        if not (obj == obj2):
            #print("obj = '%s'" % obj.toString())
            #print("obj2 = '%s'" % obj2.toString())
            dd1 = obj.toDict()
            dd2 = obj2.toDict()
            # exporting back to dicts, to see whether the DATA really is different (not just listed as diff b/c diff subobjects)
            print("dicts-from-class-objects the same? %r" % (dd1 == dd2,))
            if not (dd1 == dd2):
                print("obj2 not same as original obj and dicts show different data, too (yikes!!)")
                print("dict obj = '%s'" % str(dd1))
                print("dict obj2 = '%s'" % str(dd2))        

        # syntax to create an object from scratch
        obj = factory.createObjectByName("CMASI", "KeyValuePair")
        obj.set_Key("Hello")
        obj.set_Value("World")
        
        # syntax to send back to UxAS
        header = str(obj.FULL_LMCP_TYPE_NAME) + "$lmcp|" + str(obj.FULL_LMCP_TYPE_NAME) + "||0|0$"
        smsg = LMCPFactory.packMessage(obj, True)
        socket_send.send(header + smsg)
        print("  Sent:   " + obj.FULL_LMCP_TYPE_NAME)


