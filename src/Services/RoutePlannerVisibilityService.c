void rpvs_configure()
{
  __COPPER_HANDSHAKE__("configure");
}

void rpvs_processReceivedLmcpMessage()
{
  __COPPER_HANDSHAKE__("process");
}

void rpvs_service()
{
  rpvs_configure();
  for(;;) rpvs_processReceivedLmcpMessage();
}

