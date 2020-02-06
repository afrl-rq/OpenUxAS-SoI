import time
from pylmcp import Object
from pylmcp.server import Server
from pylmcp.uxas import AutomationRequestValidator, UxASConfig

# Create bridge configuration
bridge_cfg = UxASConfig()
bridge_cfg += AutomationRequestValidator()

with Server(bridge_cfg=bridge_cfg) as server:
    try:
        # Send messages
        for obj in (Object(class_name='AirVehicleConfiguration', ID=400,
                           randomize=True),
                    Object(class_name='AirVehicleConfiguration', ID=500,
                           randomize=True),
                    Object(class_name='AirVehicleState', ID=400,
                           randomize=True),
                    Object(class_name='AirVehicleState', ID=500,
                           randomize=True),
                    Object(class_name='KeepInZone', ZoneID=1,
                           randomize=True),
                    Object(class_name='KeepOutZone', ZoneID=2,
                           randomize=True),
                    Object(class_name='OperatingRegion', ID=3,
                           KeepInAreas=[1], KeepOutAreas=[2]),
                    Object(class_name='AngledAreaSearchTask', TaskID=1000,
                           SearchAreaID=30, randomize=True),
                    Object(class_name='TaskInitialized', TaskID=1000,
                           randomize=True)):
            server.send_msg(obj)
            time.sleep(0.1)

        obj = Object(class_name='ImpactAutomationRequest',
                     RequestID=50,
                     TrialRequest=Object
                     (class_name='cmasi.AutomationRequest',
                      TaskList=[1000], EntityList=[400, 500],
                      OperatingRegion=3, randomize=True),
                     randomize=True)
        server.send_msg(obj)

        msg = server.wait_for_msg(
            descriptor="afrl.impact.ImpactAutomationResponse",
            timeout=10.0)
        assert (msg.descriptor == "afrl.impact.ImpactAutomationResponse")
        assert (msg.obj['TrialResponse']['VehicleCommandList'] == []), \
            "%s\nvs\n%s" %\
            (msg.obj.as_dict()['TrialResponse']['VehicleCommandList'], [])
        assert (msg.obj['TrialResponse']['MissionCommandList'] == []), \
            "%s\nvs\n%s" %\
            (msg.obj.as_dict()['TrialResponse']['MissionCommandList'], [])
        print("OK")
    finally:
        print("Here")
