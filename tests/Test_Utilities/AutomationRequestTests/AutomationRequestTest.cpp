#include "gtest/gtest.h"
#include "GtestuxastestserviceServiceManagerStartAndRun.h"

#include "afrl/cmasi/AutomationResponse.h"
#include "afrl/cmasi/MissionCommand.h"
#include "afrl/cmasi/Waypoint.h"

// TEST(Parameter01,Parameter02) - Google Test Macro
// Parameter01: "test case" (name of collection of tests)
// Parameter02: "test" (name of test)
TEST(AutomationRequestTest, Test01_GoodRequest)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
    // duration_s - number of second to run UxAS
    uint32_t duration_s{6};
    // testPath - relative path to the directory containing configration and othe test files
	std::string testPath;
	// configFileName - file name of the UxAS configuration file
	std::string configFileName;
	#ifdef _WIN32
		#include "windows.h"
		SetCurrentDirectory("../../../");
	#endif
	testPath = "../tests/Test_Utilities/AutomationRequestTests/";
	configFileName = "cfg_AutomationRequest_Test01.xml";

	// uxasConfigurationFile - path and file name of the UxAS configuration file
	std::string uxasConfigurationFile = testPath + configFileName;
    // outputPath - path for saving output files
    std::string outputPath = testPath + "output/";
    // outputPath - path for saving log files
    std::string logPath = outputPath + "log/";
    // initialze the UxAS loggers
    gtestuxascommonLogManagerInitialize(logPath);
    // savedMessagesPath - the path and file name of the saved messages database are returned in this variable
    std::string savedMessagesPath;

    //**************************************************************************
    //  RUN THE TEST
    //**************************************************************************
    gtestuxastestserviceServiceManagerStartAndRun(duration_s,uxasConfigurationFile, outputPath, savedMessagesPath);

    //*************************************************************************
    //  CHECK RESULTS
    //*************************************************************************
    // use GoogleTest macros to perform tests on the output
    // CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    // and returns the number of messages with the given "description"
    //   - savedMessagesPath - the path and file name of the saved messages database
    //   - messageDescription - message description of messages to count

    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleConfiguration")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleState")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationResponse")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.KeepOutZone")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.LineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.OperatingRegion")));
    EXPECT_EQ(4,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.ServiceStatus")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AngledAreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AreaOfInterest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.ImpactLineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.LineOfInterest")));
    EXPECT_EQ(25,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanRequest")));
    EXPECT_EQ(26,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanResponse")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCostMatrix")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.SensorFootprintRequests")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskAssignmentSummary")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationRequest")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationResponse")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskInitialized")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskPlanOptions")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationResponse")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.CreateNewService")));
    
};

TEST(AutomationRequestTest, Test02_Missing_AirVehicleState)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
    // duration_s - number of second to run UxAS
    uint32_t duration_s{4};
    // testPath - relative path to the directory containing configration and othe test files
	std::string testPath;
	// configFileName - file name of the UxAS configuration file
	std::string configFileName;
	#ifdef _WIN32
		#include "windows.h"
		SetCurrentDirectory("../../../");
	#endif

	testPath = "../tests/Test_Utilities/AutomationRequestTests/";
	configFileName = "cfg_AutomationRequest_Test02.xml";

	// uxasConfigurationFile - path and file name of the UxAS configuration file
	std::string uxasConfigurationFile = testPath + configFileName;
    // outputPath - path for saving output files
    std::string outputPath = testPath + "output/";
    // outputPath - path for saving log files
    std::string logPath = outputPath + "log/";
    // initialze the UxAS loggers
    gtestuxascommonLogManagerInitialize(logPath);
    // savedMessagesPath - the path and file name of the saved messages database are returned in this variable
    std::string savedMessagesPath;

    //**************************************************************************
    //  RUN THE TEST
    //**************************************************************************
    bool isReinitialize{true};
    gtestuxastestserviceServiceManagerStartAndRun(duration_s,uxasConfigurationFile, outputPath, savedMessagesPath,isReinitialize);

    //*************************************************************************
    //  CHECK RESULTS
    //*************************************************************************
    // use GoogleTest macros to perform tests on the output
    // CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    // and returns the number of messages with the given "description"
    //   - savedMessagesPath - the path and file name of the saved messages database
    //   - messageDescription - message description of messages to count

    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleConfiguration")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleState")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationResponse")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.KeepOutZone")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.LineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.OperatingRegion")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.ServiceStatus")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AngledAreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AreaOfInterest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.ImpactLineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.LineOfInterest")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanRequest")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanResponse")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCostMatrix")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.SensorFootprintRequests")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskAssignmentSummary")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationRequest")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationResponse")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskInitialized")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskPlanOptions")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationRequest")));
    EXPECT_EQ(0,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationResponse")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.CreateNewService")));
};

TEST(AutomationRequestTest, Test03_TaskInsideKeepOutVisibility_WrongAnswer)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
    // duration_s - number of second to run UxAS
    uint32_t duration_s{6};
    // testPath - relative path to the directory containing configration and othe test files
	std::string testPath;
	//configFileName - file name of the UxAS configuration file
	std::string configFileName;
	#ifdef _WIN32
		#include "windows.h"
		SetCurrentDirectory("../../../");
	#endif

	testPath = "../tests/Test_Utilities/AutomationRequestTests/";
	configFileName = "cfg_AutomationRequest_Test03.xml";

	// uxasConfigurationFile - path and file name of the UxAS configuration file
	std::string uxasConfigurationFile = testPath + configFileName;
    // outputPath - path for saving output files
    std::string outputPath = testPath + "output/";
    // outputPath - path for saving log files
    std::string logPath = outputPath + "log/";
    // initialze the UxAS loggers
    gtestuxascommonLogManagerInitialize(logPath);
    // savedMessagesPath - the path and file name of the saved messages database are returned in this variable
    std::string savedMessagesPath;

    //**************************************************************************
    //  RUN THE TEST
    //**************************************************************************
    bool isReinitialize{true};
    gtestuxastestserviceServiceManagerStartAndRun(duration_s,uxasConfigurationFile, outputPath, savedMessagesPath,isReinitialize);

    //*************************************************************************
    //  CHECK RESULTS
    //*************************************************************************
    // use GoogleTest macros to perform tests on the output
    // CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    // and returns the number of messages with the given "description"
    //   - savedMessagesPath - the path and file name of the saved messages database
    //   - messageDescription - message description of messages to count

    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleConfiguration")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AirVehicleState")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationResponse")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.KeepOutZone")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.LineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.OperatingRegion")));
    EXPECT_EQ(5,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.ServiceStatus")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AngledAreaSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.AreaOfInterest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.ImpactLineSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.LineOfInterest")));
    EXPECT_EQ(26,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanRequest")));
    EXPECT_EQ(27,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.route.RoutePlanResponse")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.AssignmentCostMatrix")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.SensorFootprintRequests")));
    EXPECT_EQ(2,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.SensorFootprintResponse")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskAssignmentSummary")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationRequest")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskImplementationResponse")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskInitialized")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.TaskPlanOptions")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.task.UniqueAutomationResponse")));
    EXPECT_EQ(6,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.CreateNewService")));
    
};

int main(int argc, char **argv)
{
    // Build, Google Test run-time and environment tear-down
    ::testing::InitGoogleTest(&argc, argv);
    // Run the tests and return the results
    return RUN_ALL_TESTS();
}

