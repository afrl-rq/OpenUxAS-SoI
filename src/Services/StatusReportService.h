// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   StatusReportService.h
 * Author: derek
 *
 * Created on Jan 30, 2018
 */

#ifndef UXAS_STATUSREPORTSERVICE_H
#define UXAS_STATUSREPORTSERVICE_H

#include <mutex>
#include <unordered_set>
#include "ServiceBase.h"
#include "CallbackTimer.h"
#include "uxas/messages/uxnative/OnboardStatusReport.h"

namespace uxas
{
namespace service
{

/*! \class StatusReportService
 *  \brief This service reports the current status of an onboard-running UxAS instance.
 * 
 * <Service Type="StatusReportService" VehicleID="100" 
 *                                     ReportPeriod_ms="5000"
 *                                     StaleStateTime_ms="5000"
 *                                     KeepAliveExpiration_ms="7000" />
 * 
 * Options:
 *  - VehicleID - ID of vehicle for which to create a status report
 *  - ReportPeriod_ms - Time (in ms) between subsequent periodic reports
 * 
 * Subscribed Messages:
 *  - uxas::messages::uxnative::EntityJoin
 *  - uxas::messages::uxnative::EntityExit
 *  - uxas::messages::uxnative::AutopilotKeepAlive
 *  - afrl::cmasi::EntityState
 * 
 * Sent Messages:
 *  - uxas::messages::uxnative::OnboardStatusReport
 * 
 * 
 */

class StatusReportService : public ServiceBase
{
public:

    static const std::string&
    s_typeName()
    {
        static std::string s_string("StatusReportService");
        return (s_string);
    };

    static const std::vector<std::string>
    s_registryServiceTypeNames()
    {
        std::vector<std::string> registryServiceTypeNames = {s_typeName()};
        return (registryServiceTypeNames);
    };

    static const std::string&
    s_directoryName() { static std::string s_string(""); return (s_string); };

    static ServiceBase*
    create()
    {
        return new StatusReportService;
    };

    StatusReportService();

    virtual
    ~StatusReportService();

private:

    static
    ServiceBase::CreationRegistrar<StatusReportService> s_registrar;

    StatusReportService(StatusReportService const&) = delete;

    void operator=(StatusReportService const&) = delete;

    bool
    configure(const pugi::xml_node& serviceXmlNode) override;
    
    bool
    initialize() override;
    
    bool
    start() override;

    bool
    processReceivedLmcpMessage(std::unique_ptr<uxas::communications::data::LmcpMessage> receivedLmcpMessage) override;


private:

    // Options
    /*! \brief Vehicle ID for which the report should be generated */
    int64_t m_vehicleId{0};
    /*! \brief Period (in ms) at which the report should be sent */
    uint32_t m_reportPeriod_ms{5000};
    /*! \brief Time after which state is considered stale if no longer received */
    uint32_t m_staleStateTime_ms{5000};
    /*! \brief Time after which keep-alive is considered invalid if subsequent keep-alive not received */
    uint32_t m_keepAliveExpirationTime_ms{7000};
    
    // Timers
    /*! \brief This timer is used periodically send report messages */
    uint64_t m_reportTimerId{0};
    /*! \brief Callback for sending the status report */
    void OnReportTimeout();
    
    /*! \brief This timer is used track expiration of 'keep alive' messages */
    uint64_t m_keepAliveTimerId{0};
    /*! \brief Callback for expiration of keep-alive */
    void OnKeepAliveTimeout();
    
    /*! \brief This timer is used track staleness of state messages */
    uint64_t m_staleStateTimerId{0};
    /*! \brief Callback for identifying stale state */
    void OnStaleStateTimeout();
    
    // Support
    /*! \brief Mutex for protecting update/send of report */
    std::mutex m_mutex;
    /*! \brief Connectivity tracking */
    std::unordered_set<uint64_t> m_connections;
    /*! \brief Constantly updated report to be sent at requested frequency */
    uxas::messages::uxnative::OnboardStatusReport m_report;
};

}; //namespace service
}; //namespace uxas

#endif /* UXAS_STATUSREPORTSERVICE_H */

