#include "gtest/gtest.h"

#include "uxas/project/vics/VicsBase.h"

#include "LmcpObjectNetworkClientBase.h"

#include "UxAS_Log.h"
#include "UxAS_LogManagerDefaultInitializer.h"

#include "stdUniquePtr.h"

#include <chrono>

class GtestuxastestserviceLmcpObjectNetworkClient : public uxas::communications::LmcpObjectNetworkClientBase
{
public:
    static const std::string&
    s_typeName() { static std::string s_string("GtestuxastestserviceLmcpObjectNetworkClient"); return (s_string); };

    GtestuxastestserviceLmcpObjectNetworkClient();

    virtual
    ~GtestuxastestserviceLmcpObjectNetworkClient();

private:

    /** \brief Copy construction not permitted */
    GtestuxastestserviceLmcpObjectNetworkClient(GtestuxastestserviceLmcpObjectNetworkClient const&) = delete;

    /** \brief Copy assignment operation not permitted */
    void operator=(GtestuxastestserviceLmcpObjectNetworkClient const&) = delete;

public:

    bool
    configureLmcpObjectNetworkClient();

    bool
    initializeLmcpObjectNetworkClient();
    
    bool
    sendVicsMessagesWithUniqueId(std::shared_ptr<uxas::project::vics::VicsBase> vicsBase, const uint32_t sendCount);

    bool
    sendVicsMessagesWithUniqueId(std::shared_ptr<uxas::project::vics::VicsBase> vicsBase, const uint32_t sendCount, std::chrono::milliseconds delay_ms);

    std::chrono::milliseconds m_defaultSendMessageDelay_ms{1};

    bool m_isInitialized{false};
};

GtestuxastestserviceLmcpObjectNetworkClient::GtestuxastestserviceLmcpObjectNetworkClient()
{
};

GtestuxastestserviceLmcpObjectNetworkClient::~GtestuxastestserviceLmcpObjectNetworkClient()
{
};

bool
GtestuxastestserviceLmcpObjectNetworkClient::configureLmcpObjectNetworkClient()
{
    UXAS_LOG_DEBUG_VERBOSE_TESTFRAMEWORK(s_typeName(), "::configure method START");
    bool isSuccess{false};
    pugi::xml_node dummyXmlNode;
    isSuccess = configureNetworkClient(s_typeName(), uxas::communications::LmcpObjectNetworkClientBase::ReceiveProcessingType::SERIALIZED_LMCP, dummyXmlNode);
    return (isSuccess);
};

bool
GtestuxastestserviceLmcpObjectNetworkClient::initializeLmcpObjectNetworkClient()
{
    UXAS_LOG_DEBUG_VERBOSE_TESTFRAMEWORK(s_typeName(), "::initializeLmcpObjectNetworkClient method START");
    m_isInitialized = initializeAndStart();
    return (m_isInitialized);
};

bool
GtestuxastestserviceLmcpObjectNetworkClient::sendVicsMessagesWithUniqueId(std::shared_ptr<uxas::project::vics::VicsBase> vicsBase, const uint32_t sendCount)
{
    sendVicsMessagesWithUniqueId(vicsBase, sendCount, m_defaultSendMessageDelay_ms);
};

bool
GtestuxastestserviceLmcpObjectNetworkClient::sendVicsMessagesWithUniqueId(std::shared_ptr<uxas::project::vics::VicsBase> vicsBase, const uint32_t sendCount, std::chrono::milliseconds delay_ms)
{
    if (m_isInitialized)
    {
        for (size_t sendCnt = 0; sendCnt < sendCount; sendCnt++)
        {
            int64_t uniqueMsgId = getUniqueEntitySendMessageId();
            UXAS_LOG_DEBUG_VERBOSE_TESTFRAMEWORK(s_typeName(), ":: sendVicsMessagesWithUniqueId sending VICS ", vicsBase->getLmcpTypeName(), " with message ID ", uniqueMsgId);
            vicsBase->setMessageID(uniqueMsgId);
            sendSharedLmcpObjectBroadcastMessage(vicsBase);
            std::this_thread::sleep_for(delay_ms);
        }
    }
    else
    {
        UXAS_LOG_WARN(s_typeName(), ":: sendVicsMessagesWithUniqueId failed to send VICS ", vicsBase->getLmcpTypeName(), " messages since not initialize");
    }
};
