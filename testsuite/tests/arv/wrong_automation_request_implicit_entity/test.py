from pylmcp import Object
from pylmcp.server import Server
from pylmcp.uxas import AutomationRequestValidator, UxASConfig

# Create bridge configuration
bridge_cfg = UxASConfig()
bridge_cfg += AutomationRequestValidator()

with Server(bridge_cfg=bridge_cfg) as server:
    try:
        obj = Object(class_name='cmasi.AutomationRequest', EntityList=[],
                     randomize=True)
        server.send_msg(obj)

        msg = server.wait_for_msg(descriptor="afrl.cmasi.AutomationResponse",
                                  timeout=5.0)
        assert (msg.descriptor == "afrl.cmasi.AutomationResponse")
        assert (msg.obj['VehicleCommandList'] == []), \
            "%s\nvs\n%s" % (msg.obj.as_dict()['VehicleCommandList'], [])
        assert (msg.obj['MissionCommandList'] == []), \
            "%s\nvs\n%s" % (msg.obj.as_dict()['MissionCommandList'], [])

        for obj in (Object(class_name='AirVehicleConfiguration', ID=400,
                           randomize=True),
                    Object(class_name='AirVehicleState', ID=500,
                           randomize=True),
                    Object(class_name='cmasi.AutomationRequest', EntityList=[],
                           randomize=True)):
            server.send_msg(obj)

        msg = server.wait_for_msg(descriptor="afrl.cmasi.AutomationResponse",
                                  timeout=5.0)
        assert (msg.descriptor == "afrl.cmasi.AutomationResponse")
        assert (msg.obj['VehicleCommandList'] == []), \
            "%s\nvs\n%s" % (msg.obj.as_dict()['VehicleCommandList'], [])
        assert (msg.obj['MissionCommandList'] == []), \
            "%s\nvs\n%s" % (msg.obj.as_dict()['MissionCommandList'], [])
        print("OK")
    finally:
        print("Here")
