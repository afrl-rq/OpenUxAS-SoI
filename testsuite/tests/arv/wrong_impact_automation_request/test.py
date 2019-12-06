from pylmcp import Object
from pylmcp.server import Server
from pylmcp.uxas import AutomationRequestValidator, UxASConfig

# Create bridge configuration
bridge_cfg = UxASConfig()
bridge_cfg += AutomationRequestValidator()

with Server(bridge_cfg=bridge_cfg) as server:
    try:
        obj = Object(class_name='afrl.impact.ImpactAutomationRequest',
                     randomize=True)
        server.send_msg(obj)

        msg = server.wait_for_msg(
            descriptor="afrl.impact.ImpactAutomationResponse",
            timeout=5.0)
        assert (msg.descriptor == "afrl.impact.ImpactAutomationResponse")
        assert (cmp(msg.obj.as_dict()['VehicleCommandList'], []) == 1), \
            "%s\nvs\n%s" % (msg.obj.as_dict()['VehicleCommandList'], [])
        assert (cmp(msg.obj.as_dict()['MissionCommandList'], []) == 1), \
            "%s\nvs\n%s" % (msg.obj.as_dict()['MissionCommandList'], [])
    finally:
        print "Here"
