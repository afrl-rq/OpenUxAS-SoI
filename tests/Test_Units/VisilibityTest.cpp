#include "gtest/gtest.h"

#include "visilibity.h"
#include "TestReport.h"

using namespace VisiLibity;
using namespace test;

class TestShape
{
public:
    //Default constructor
    TestShape(){};
    //Overloaded constructor
    TestShape(std::vector<VisiLibity::Polygon> original, std::vector<VisiLibity::Polygon> expected, std::shared_ptr<report::Report> testReport)
    {
        m_originalPolygonList = original;
        m_expectedPolygonList = expected;
        m_report = testReport;
    }
    std::vector<VisiLibity::Polygon> m_originalPolygonList;
    std::vector<VisiLibity::Polygon> m_expectedPolygonList;
    std::shared_ptr<report::Report> m_report;
    //define threshold - polygons within this distance of each other will be considered to be adjacent
    double m_epsilon = 0.05;
    void runTest(std::string description)
    {
        std::vector<VisiLibity::Polygon> actualPolygonList;
        Polygon::union_(m_originalPolygonList,actualPolygonList,m_epsilon);
    
        //make sure there are no extraneous polygons in the list
        EXPECT_EQ(m_expectedPolygonList.size(), actualPolygonList.size());
        
        //get length of shorter of two polygon lists, in case above check fails
        int n_toCompare = std::min(m_expectedPolygonList.size(), actualPolygonList.size());
        //compare actual to expected results for each polygon
        for (int polyIdx = 0; polyIdx < n_toCompare; polyIdx++)
        {
            EXPECT_TRUE(VisiLibity::equivalent(actualPolygonList[polyIdx], m_expectedPolygonList[polyIdx], m_epsilon));
        }

        //Add to report
        m_report->addLine(description);

        //Expected Results
        std::vector<report::Plot_Polygon> expectedPolyList;
        for (auto &poly : m_originalPolygonList)
        {
            // old polygons are red
            expectedPolyList.push_back(report::Plot_Polygon(poly, 1, "red", "solid", "thick"));
        }

        for (auto &poly : m_expectedPolygonList)
        {
            //new polygons are blue
            expectedPolyList.push_back(report::Plot_Polygon(poly, 1, "blue", "dashed", "ultra thick"));
        }

        report::Plot expectedPlot(expectedPolyList, "Expected Result");
        m_report->addPlot(expectedPlot);

        //Actual Results
        std::vector<report::Plot_Polygon> actualPolyList;
        for (auto &poly : m_originalPolygonList)
        {
            // old polygons are red
            actualPolyList.push_back(report::Plot_Polygon(poly, 1, "red", "solid", "thick"));
        }

        for (auto &poly : actualPolygonList)
        {
            //new polygons are blue
            actualPolyList.push_back(report::Plot_Polygon(poly, 1, "blue", "dashed", "ultra thick"));
        }
        report::Plot actualPlot(actualPolyList, "Actual Result");
        m_report->addPlot(actualPlot);
        
    };
};

TEST(VisiLibityTest, Polygon_union)
{
    //test::report::Report report(std::string("Polygon_union"));
    auto testReport = std::make_shared<report::Report>("VisiLibity");
    {
        /// First test is two overlapping polygons that result in a single polygon
        // basic shape (not to scale):
        //              _______
        //             |       |
        //             |      _|_______
        //             |     | |       |
        //              -------        |
        //                   |         |
        //                   |_________|
        
        //first polygon to merge
        VisiLibity::Polygon polygon1(std::vector<Point>{Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 5.0), Point(0.0, 5.0) });
        //second polygon to merge
        VisiLibity::Polygon polygon2(std::vector<Point>{Point(2.0, 0.0), Point(5.0, 0.0), Point(5.0, 3.0), Point(2.0, 3.0) });
        
        //expected new polygon after merge
        VisiLibity::Polygon newPolygon(std::vector<Point>{Point(3.0, 3.0), Point(3.0, 5.0), Point(0.0, 5.0), Point(0.0, 2.0), Point(2.0, 2.0), Point(2.0, 0.0), Point(5.0, 0.0), Point(5.0, 3.0)});
        
        //merge function arguments are vectors of polygons
        //expected function output polygon list
        std::vector<Polygon> expPolygonList;
        expPolygonList.push_back(newPolygon);
        
        //function input polygon list
        std::vector<VisiLibity::Polygon> originalPolygonList;
        originalPolygonList.push_back(polygon1);
        originalPolygonList.push_back(polygon2);
        
        TestShape ts(originalPolygonList, expPolygonList, testReport);
        ts.runTest("Test 1: Merging two overlapping polygons");
        if(Test::HasNonfatalFailure())
        {
            testReport->addLine("Test Fails", "red");
        }
        else
        {
            testReport->addLine("Test Passes", "green");
        }
            
    }
    
        ///Second test is merging two overlapping keep-in polygons that create a single keep-out "hole"
        //Basic shape: (not to scale)
        //          _____
        //         |     |
        //         |     |
        //  _______|__   |
        // |          |  |
        // |          |  |
        // |      ____|  |
        // |     | |     |
        // |     | |     |
        // |     | |     |
        // |     |_|__   |
        // |          |  |
        // |          |  |
        // |          |  |
        // |__________|  |
        //         |_____|
        //

    {
        //first polygon to merge
        VisiLibity::Polygon polygon1(std::vector<Point>{Point(3.0, 1.0), Point(3.0, 2.0), Point(1.0, 2.0), Point(1.0, 3.0), Point(3.0, 3.0), Point(3.0, 4.0), Point(0.0, 4.0), Point(0.0, 1.0)});
        //second polygon to merge
        VisiLibity::Polygon polygon2(std::vector<Point>{Point(2.0, 5.0), Point(4.0, 5.0), Point(4.0, 0.0), Point(2.0, 0.0)});
        
        //expected new polygon after merge
        VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(0.0, 1.0), Point(0.0, 4.0), Point(2.0, 4.0), Point(2.0, 5.0), Point(4.0, 5.0), Point(4.0, 00), Point(2.0, 0.0), Point(2.0, 1.0)});
        
        //expected keep-out "hole" created
        //CCW order?
        VisiLibity::Polygon newPolygon2(std::vector<Point>{Point(1.0, 2.0), Point(2.0, 2.0), Point(2.0, 3.0), Point(1.0, 3.0)});
        
        //merge function arguments are vectors of polygons
        //expected function output polygon list
        std::vector<Polygon> expPolygonList;
        expPolygonList.push_back(newPolygon1);
        expPolygonList.push_back(newPolygon2);
        
        //function input polygon list
        std::vector<VisiLibity::Polygon> originalPolygonList;
        originalPolygonList.push_back(polygon1);
        originalPolygonList.push_back(polygon2);
        
        TestShape ts(originalPolygonList, expPolygonList, testReport);
        ts.runTest("Test 2: merging two overlapping keep-in polygons that create a single keep-out 'hole'");
        if(Test::HasNonfatalFailure())
        {
            testReport->addLine("Test Fails", "red");
        }
        else
        {
            testReport->addLine("Test Passes", "green");
        }
    }

    //TODO: Implement TEST 3 iff we implement keep-in/keep-out based on CW/CCW polygon direction

//        ///This test is merging two overlapping keep-out polygons that create a single "hole" that is ignored because you can never reach it
//        //          _____
//        //         |     |
//        //         |     |
//        //  _______|__   |
//        // |          |  |
//        // |          |  |
//        // |      ____|  |
//        // |     | |     |
//        // |     | |     |
//        // |     | |     |
//        // |     |_|__   |
//        // |          |  |
//        // |          |  |
//        // |          |  |
//        // |__________|  |
//        //         |_____|
//  {
//        //first polygon to merge
//        VisiLibity::Polygon polygon1(std::vector<Point>{Point(3.0, 1.0), Point(3.0, 2.0), Point(1.0, 2.0), Point(1.0, 3.0), Point(3.0, 3.0), Point(3.0, 4.0), Point(0.0, 4.0), Point(0.0, 1.0)});
//        //second polygon to merge
//        VisiLibity::Polygon polygon2(std::vector<Point>{Point(2.0, 5.0), Point(4.0, 5.0), Point(4.0, 0.0), Point(2.0, 0.0)});
//
//        //expected new polygon after merge
//        VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(0.0, 1.0), Point(0.0, 4.0), Point(2.0, 4.0), Point(2.0, 5.0), Point(4.0, 5.0), Point(4.0, 00), Point(2.0, 0.0), Point(2.0, 1.0)});
//
//        //expected keep-in "hole" created, but ignored
//        //CCW order
//        VisiLibity::Polygon newPolygon2(std::vector<Point>{Point(1.0, 2.0), Point(2.0, 2.0), Point(2.0, 3.0), Point(1.0, 3.0)});
//
//
//        //merge function arguments are vectors of polygons
//        //expected function output polygon list
//        std::vector<Polygon> expPolygonList;
//        expPolygonList.push_back(newPolygon1);
//        expPolygonList.push_back(newPolygon2);
//
//        //function input polygon list
//        std::vector<VisiLibity::Polygon> originalPolygonList;
//        originalPolygonList.push_back(polygon1);
//        originalPolygonList.push_back(polygon2);
//
//        TestShape ts(originalPolygonList, expPolygonList, testReport);
//        ts.runTest("Test 3: Merging two overlapping polygons with hole in middle that will be ignored because it is unreachable");
//        if(Test::HasNonfatalFailure())
//        {
//            testReport->addLine("Test Fails", "red");
//        }
//        else
//        {
//            testReport->addLine("Test Passes", "green");
//        }
//    }
    
    ///Third test is merging polygons that are not adjacent and do not overlap. Distance is greater than epsilon
    // basic shape (not to scale):
    //              _______
    //             |       |
    //             |       |  _________
    //             |       | |         |
    //              -------  |         |
    //                       |         |
    //                       |_________|
    {
        //first polygon to merge
        VisiLibity::Polygon polygon1(std::vector<Point>{Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 5.0), Point(0.0, 5.0) });
        //second polygon to merge
        VisiLibity::Polygon polygon2(std::vector<Point>{Point(4, 0.0), Point(7, 0.0), Point(7, 3.0), Point(4, 3.0) });
        
        //expected new polygons after merge - both unchanged from original
        VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 5.0), Point(0.0, 5.0) });
        VisiLibity::Polygon newPolygon2(std::vector<Point>{Point(4, 0.0), Point(7, 0.0), Point(7, 3.0), Point(4, 3.0) });
        
        //merge function arguments are vectors of polygons
        //expected function output polygon list
        std::vector<Polygon> expPolygonList;
        expPolygonList.push_back(newPolygon1);
        expPolygonList.push_back(newPolygon2);
        
        //function input polygon list
        std::vector<VisiLibity::Polygon> originalPolygonList;
        originalPolygonList.push_back(polygon1);
        originalPolygonList.push_back(polygon2);
        
        TestShape ts(originalPolygonList, expPolygonList, testReport);
        ts.runTest("Test 3: Attempt to merge two non-adjacent polygons");
        if(Test::HasNonfatalFailure())
        {
            testReport->addLine("Test Fails", "red");
        }
        else
        {
            testReport->addLine("Test Passes", "green");
        }
        
    }
    
    ///Fourth test is merging polygons that are not adjacent and do not overlap, however the distance is less than epsilon. The result is a merged polygon.s
    // basic shape (not to scale):
    //              _______
    //             |       |
    //             |       | _________
    //             |       ||         |
    //              ------- |         |
    //                      |         |
    //                      |_________|
    {
        //first polygon to merge
        VisiLibity::Polygon polygon1(std::vector<Point>{Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 5.0), Point(0.0, 5.0) });
        //second polygon to merge
        VisiLibity::Polygon polygon2(std::vector<Point>{Point(3.04, 0.0), Point(6.0, 0.0), Point(6.0, 3.0), Point(3.04, 3.0) });
        
        //expected new polygon after merge
        VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(3.0, 3.0), Point(3.0, 5.0), Point(0.0, 5.0), Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 0.0), Point(6.0, 0.0), Point(6.0, 3.0)});
        
        //merge function arguments are vectors of polygons
        //expected function output polygon list
        std::vector<Polygon> expPolygonList;
        expPolygonList.push_back(newPolygon1);
        
        //function input polygon list
        std::vector<VisiLibity::Polygon> originalPolygonList;
        originalPolygonList.push_back(polygon1);
        originalPolygonList.push_back(polygon2);
        
        TestShape ts(originalPolygonList, expPolygonList, testReport);
        ts.runTest("Test 4: Merging two non-adjacent polygons that are within epsilon distance");
        if(Test::HasNonfatalFailure())
        {
            testReport->addLine("Test Fails", "red");
        }
        else
        {
            testReport->addLine("Test Passes", "green");
        }
        
    }
    
    ///Fifth test is merging 3 overlaping polygons
    // basic shape (not to scale):
    //                  ______
    //              ___|___   |
    //             |   |   |  |
    //             |   |  _|__|____
    //             |   | | |  |    |
    //              -------   |    |
    //                 |_|____|    |
    //                   |_________|
    
    {
        //first polygon to merge
        VisiLibity::Polygon polygon1(std::vector<Point>{Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 5.0), Point(0.0, 5.0) });
        //second polygon to merge
        VisiLibity::Polygon polygon2(std::vector<Point>{Point(2.0, 0.0), Point(5.0, 0.0), Point(5.0, 3.0), Point(2.0, 3.0) });
        //third polygon to merge
        VisiLibity::Polygon polygon3(std::vector<Point>{Point(1.0, 1.0), Point(4.0, 1.0), Point(4.0, 6.0), Point(1.0, 6.0)});
    
        
        //expected new polygon after merge
        VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(0.0, 2.0), Point(0.0, 5.0), Point(1.0, 5.0), Point(1.0, 6.0), Point(4.0, 6.0), Point(4.0, 3.0), Point(5.0, 3.0), Point(5.0, 0.0), Point(2.0, 0.0), Point(2.0, 1.0), Point(1.0, 1.0), Point(1.0, 2.0)});
        
        //merge function arguments are vectors of polygons
        //expected function output polygon list
        std::vector<Polygon> expPolygonList;
        expPolygonList.push_back(newPolygon1);
        
        //function input polygon list
        std::vector<VisiLibity::Polygon> originalPolygonList;
        originalPolygonList.push_back(polygon1);
        originalPolygonList.push_back(polygon2);
        originalPolygonList.push_back(polygon3);
        
        TestShape ts(originalPolygonList, expPolygonList, testReport);
        ts.runTest("Test 5: Merging three overlapping polygons");
        if(Test::HasNonfatalFailure())
        {
            testReport->addLine("Test Fails", "red");
        }
        else
        {
            testReport->addLine("Test Passes", "green");
        }
    }
    testReport->render();
};

int main(int argc, char **argv)
{
    // Build, Google Test run-time and environment tear-down
    ::testing::InitGoogleTest(&argc, argv);
    // Run the tests and return the results
    return RUN_ALL_TESTS();
}

