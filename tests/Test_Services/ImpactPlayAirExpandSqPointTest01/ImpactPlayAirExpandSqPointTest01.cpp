#include "gtest/gtest.h"
#include "GtestuxastestserviceServiceManagerStartAndRun.h"
 
// TEST(Parameter01,Parameter02) - Google Test Macro
// Parameter01: "test case" (name of collection of tests)
// Parameter02: "test" (name of test)
TEST(ImpactPlayAirExpandSqPointTest01, InitialTest)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
	// duration_s - number of second to run UxAS
    uint32_t duration_s{5};
    // testPath - relative path to the directory containing configration and othe test files
	std::string testPath;
	// configFileName - the file name of the UxAS configuration file
	std::string configFileName;
	#ifdef _WIN32
		#include "windows.h"
		SetCurrentDirectory("../../../");
	#endif

	testPath = "../tests/Test_Services/ImpactPlayAirExpandSqPointTest01/";
	configFileName = "cfg_Test01.xml";

	// uxasConfigurationFile - path and file name of the UxAS configuration file
	std::string uxasConfigurationFile = testPath + configFileName;
    // outputPath - path for saving output files
    std::string outputPath = testPath + "/output/";
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

    /**************************************************************************
    *  CHECK RESULTS
    ***************************************************************************
    * use GoogleTest macros to perform tests on the output
    * CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    * 	and returns the number of messages with the given "description"
    * - savedMessagesPath - the path and file name of the saved messages database
    * - messageDescription - message description of messages to count
	*
	*	ASSERT_TRUE - Google Test Macro
    */
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.PointOfInterest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.impact.PatternSearchTask")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationRequest")));
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.AutomationResponse")));

};

int main(int argc, char **argv)
{
    // Build, Google Test run-time and environment tear-down
    ::testing::InitGoogleTest(&argc, argv);
    // Run the tests and return the results
    int32_t results{RUN_ALL_TESTS()};

    return(results);    
    
}

