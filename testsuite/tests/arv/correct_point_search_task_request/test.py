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
                    Object(class_name='PointOfInterest', PointID=30,
                           randomize=True),
                    Object(class_name='ImpactPointSearchTask', TaskID=1000,
                           SearchLocationID=30, randomize=True),
                    Object(class_name='TaskInitialized', TaskID=1000,
                           randomize=True)):
            server.send_msg(obj)
            time.sleep(0.1)

        obj = Object(class_name='ImpactAutomationRequest',
                     RequestID=50,
                     TrialRequest=Object(class_name='cmasi.AutomationRequest',
                                         TaskList=[1000],
                                         EntityList=[400, 500],
                                         OperatingRegion=3, randomize=True),
                     randomize=True)
        server.send_msg(obj)

        msg = server.wait_for_msg(
            descriptor='uxas.messages.task.UniqueAutomationRequest',
            timeout=10.0)
        assert(msg.descriptor == "uxas.messages.task.UniqueAutomationRequest")
        assert(msg.obj['OriginalRequest'] == obj['TrialRequest']),\
            "%s\nvs\n%s" % \
            (msg.obj.as_dict()['OriginalRequest'], obj.as_dict())
        unique_id = msg.obj.data["RequestID"]

        # UniqueAutomationReponse
        obj = Object(
            class_name='uxas.messages.task.UniqueAutomationResponse',
            ResponseID=unique_id, randomize=True)
        server.send_msg(obj)

        msg = server.wait_for_msg(
            descriptor="afrl.impact.ImpactAutomationResponse",
            timeout=10.0)
        assert (msg.descriptor == "afrl.impact.ImpactAutomationResponse")
        assert (msg.obj['TrialResponse'] == obj['OriginalResponse']),\
            "%s\nvs\n%s" %\
            (msg.obj.as_dict(), obj.as_dict()['OriginalResponse'])
        print("OK")
    finally:
        print("Here")
