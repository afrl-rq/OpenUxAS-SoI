// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#include "ServiceBase.h"

#include "UxAS_ConfigurationManager.h"
#include "Constants/UxAS_String.h"

#include "FileSystemUtilities.h"

#include <sstream>

namespace uxas
{
namespace service
{


    ServiceBase::ServiceBase(const std::string& serviceType, const std::string& workDirectoryName)
    : m_serviceType(serviceType), m_workDirectoryName(workDirectoryName)
    {
        m_serviceId = m_networkId;
        UXAS_LOG_INFORM(m_serviceType, "::ServiceBase set service ID to LMCP network ID value ", m_networkId);
    };

    ServiceBase::~ServiceBase()
    {
//        UXAS_LOG_INFORM_ASSIGNMENT(m_serviceType, "::~ServiceBase()");     
    };


bool
ServiceBase::configureService(const std::string& parentOfWorkDirectory, const std::string& serviceXml)
{
    pugi::xml_document xmlDoc;
    if (xmlDoc.load(serviceXml.c_str()))
    {
    	return (configureService(parentOfWorkDirectory, xmlDoc.root()));
	}

    return false;
};

bool
ServiceBase::configureService(const std::string& parentWorkDirectory, const pugi::xml_node& serviceXmlNode)
{
    UXAS_LOG_DEBUGGING(m_serviceType, "::configureService method START");
    bool isSuccess{false};

    if (!m_workDirectoryName.empty())
    {
        
        m_workDirectoryPath = parentWorkDirectory + ((*(parentWorkDirectory.rbegin()) == '/') ? "" : "/")
                + m_workDirectoryName + ((*(m_workDirectoryName.rbegin()) == '/') ? "" : "/");

    }
    else
    {
        m_workDirectoryPath = "";
    }

    isSuccess = configureNetworkClient(m_serviceType, m_receiveProcessingType, serviceXmlNode);

    //
    // DESIGN 20150911 RJT message addressing - service group (multi-cast)
    // - sent messages always include source group value (empty or non-empty)
    // - services can have empty or non-empty source group value
    // - bridges always have empty source group value
    // - services with non-empty source group value are automatically subscribed to the source group value (to receive multi-cast messages)
    //
    if (!serviceXmlNode.attribute(uxas::common::StringConstant::MessageGroup().c_str()).empty())
    {
        // set source group value that will be assigned to source group field of sent messages
        m_messageSourceGroup = serviceXmlNode.attribute(uxas::common::StringConstant::MessageGroup().c_str()).value();
        UXAS_LOG_INFORM(m_serviceType, "::configureService setting m_messageSourceGroup to [", m_messageSourceGroup, "] from XML configuration");
        // subscribe to messages addressed to non-empty source group value
        if (!m_messageSourceGroup.empty())
        {
            addSubscriptionAddress(m_messageSourceGroup);
        }
    }
    else
    {
        UXAS_LOG_INFORM(m_serviceType, "::configureService did not find ", uxas::common::StringConstant::MessageGroup(), " value in XML configuration");
    }
    
    if (isSuccess)
    {
        m_isConfigured = true;
        UXAS_LOG_INFORM(m_serviceType, "::configureService succeeded - service ID ", m_serviceId);
    }
    else
    {
        UXAS_LOG_ERROR(m_serviceType, "::configureService failed - service ID ", m_serviceId);
    }

    UXAS_LOG_DEBUGGING(m_serviceType, "::configureService method END");
    return (isSuccess);
};

bool
ServiceBase::initializeAndStartService()
{
    bool isSuccess{false};

    if (m_isConfigured)
    {
        if (!m_workDirectoryPath.empty())
        {
            std::stringstream errors;
            isSuccess = uxas::common::utilities::c_FileSystemUtilities::bCreateDirectory(m_workDirectoryPath, errors);
            if (isSuccess)
            {
                UXAS_LOG_INFORM(m_serviceType, "::initializeAndStartService created work directory ", m_workDirectoryPath, " - service ID ", m_serviceId);
            }
            else
            {
                UXAS_LOG_ERROR(m_serviceType, "::initializeAndStartService failed to create work directory ", m_workDirectoryPath, " - service ID ", m_serviceId);
            }
        }
        else
        {
            isSuccess = true;
            UXAS_LOG_INFORM(m_serviceType, "::initializeAndStartService skipping work directory creation - service ID ", m_serviceId);
        }

        if (isSuccess)
        {
            isSuccess = initializeAndStart();
        }

        if (isSuccess)
        {
            UXAS_LOG_INFORM(m_serviceType, "::initializeAndStartService succeeded - service ID ", m_serviceId);
        }
        else
        {
            UXAS_LOG_ERROR(m_serviceType, "::initializeAndStartService failed - service ID ", m_serviceId);
        }
    }
    else
    {
        UXAS_LOG_ERROR(m_serviceType, "::initializeAndStartService failed since configure method has not been invoked");
    }

    return (isSuccess);
};

}; //namespace service
}; //namespace uxas
