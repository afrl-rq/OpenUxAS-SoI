import time
from pylmcp import Object
from pylmcp.server import Server
from pylmcp.uxas import AutomationRequestValidator, UxASConfig

# Create bridge configuration
bridge_cfg = UxASConfig()
bridge_cfg += AutomationRequestValidator()

with Server(bridge_cfg=bridge_cfg) as server:
    try:
        obj = Object(class_name='ServiceStatus', StatusType=2,
                     randomize=True)
        server.send_msg(obj)
        time.sleep(1)
        print("OK")
    finally:
        print("Here")
