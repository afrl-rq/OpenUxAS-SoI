int uxas_env()
{
    int x;
    while(1)
    {
        x = __COPPER_NONDET__();
        if(x)
            __COPPER_HANDSHAKE__("route_request");
        else
            __COPPER_HANDSHAKE__("route_response");
    }
    
    return 0;
}
