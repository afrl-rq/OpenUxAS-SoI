#include "gtest/gtest.h"
#include "GtestuxastestserviceServiceManagerStartAndRun.h"
 
// TEST(Parameter01,Parameter02) - Google Test Macro
// Parameter01: "test case" (name of collection of tests)
// Parameter02: "test" (name of test)
TEST(HelloWorld_Test01, CorrectNumberMessages)
{
    //**************************************************************************
    //  INITIALIZE TEST SETUP
    //**************************************************************************
	// duration_s - number of second to run UxAS
    uint32_t duration_s{13}; // this test seems to take ~14.9s to send 10 messages on bash Ubuntu instances; it's about 8-10 msgs for duration 13, depending; this test is a bit odd because it keeps sending msgs until UxAS stops but test is for a certain number of sent messages only...
    // testPath - relative path to the directory containing configration and other test files
	std::string testPath;
	#ifdef _WIN32
		#include "windows.h"
		SetCurrentDirectory("../../../../");
	#endif

	testPath = "../tests/Test_Services/00_ExampleTests/01_Test_HelloWorld/";

    // uxasConfigurationFile - path and file name of the UxAS configuration file
    std::string uxasConfigurationFile = testPath + "cfg_HelloWorld.xml";
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

    /**************************************************************************
    *  CHECK RESULTS
    ***************************************************************************
    * use GoogleTest macros to perform tests on the output
    * CountMessagesInLogDb(savedMessagesPath,messageDescription) - queries the saved messages database 
    * 	and returns the number of messages with the given "description"
    * - savedMessagesPath - the path and file name of the saved messages database
    * - messageDescription - message description of messages to count
	*
	*	EXPECT_EQ - Google Test Macro
    */
    EXPECT_EQ(1,CountMessagesInLogDb(savedMessagesPath, std::string("uxas.messages.uxnative.StartupComplete")));
    EXPECT_NEAR(9,CountMessagesInLogDb(savedMessagesPath, std::string("afrl.cmasi.KeyValuePair")),1); // should be 9 +- 1, so a range from 8 to 10 messages in 13s
};

int main(int argc, char **argv)
{
	 // Build, Google Test run-time and environment tear-down
    ::testing::InitGoogleTest(&argc, argv);
    // Run the tests and return the results
    return RUN_ALL_TESTS();
}

