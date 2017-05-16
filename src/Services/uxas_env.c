int uxas_env()
{
    for(;;)
    {
        if(__COPPER_NONDET__())
            __COPPER_HANDSHAKE__("route_request");
        else
            __COPPER_HANDSHAKE__("route_response");
    }
    
    return 0;
}
