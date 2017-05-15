void ras_configure()
{
  __COPPER_HANDSHAKE__("configure");
}

void ras_processReceivedLmcpMessage()
{
  __COPPER_HANDSHAKE__("process");
}

void ras_service()
{
  ras_configure();
  for(;;) ras_processReceivedLmcpMessage();
}

