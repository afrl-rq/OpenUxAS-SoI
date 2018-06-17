#include "gtest/gtest.h"

#include "visilibity.h"
#include "TestReport.h"

using namespace VisiLibity;
using namespace test;

//class testShape
//{
//public:
 //   testShape();
 //   void runTest()
 //   {
        
 //   };
//}

TEST(VisiLibityTest, Polygon_union)
{
    //test::report::Report report(std::string("Polygon_union"));
    report::Report testReport("VisiLibity");

    //define threshold - polygons within this distance of each other will be considered to be adjacent
    double epsilon = 0.05;
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
        std::vector<Polygon> expMergedPolygonList;
        expMergedPolygonList.push_back(newPolygon);
        
        //function input polygon list
        std::vector<VisiLibity::Polygon> oldPolygonList;
        oldPolygonList.push_back(polygon1);
        oldPolygonList.push_back(polygon2);
        
        //create resulting polygon list
        std::vector<VisiLibity::Polygon> newPolygonList;

        //test
        Polygon::union_(oldPolygonList,newPolygonList,epsilon);
        //compare actual to expected results
        //EXPECT_TRUE(newPolygonList[0] == expMergedPolygonList[0]);
        EXPECT_TRUE(VisiLibity::equivalent(newPolygonList[0], expMergedPolygonList[0], epsilon));
        //make sure there are no extraneous polygons in the list
        //TODO: use method n?
        EXPECT_EQ(expMergedPolygonList.size(), newPolygonList.size());
        
        //Add to report
        testReport.addText("Test 1: Merging two overlapping polygons");
        
        //Expected Results
        std::vector<report::Plot_Polygon> expectedPolyList;
        for (auto &poly : oldPolygonList)
        {
            // old polygons are red
            expectedPolyList.push_back(report::Plot_Polygon(poly, 1, "red", "solid"));
        }
        
        for (auto &poly : expMergedPolygonList)
        {
            //new polygons are blue
            expectedPolyList.push_back(report::Plot_Polygon(poly, 1, "blue", "loosely dotted"));
        }
        
        report::Plot expectedPlot(expectedPolyList, "Expected Result");
        testReport.addPlot(expectedPlot);
        
        //Actual Results
        std::vector<report::Plot_Polygon> actualPolyList;
        for (auto &poly : oldPolygonList)
        {
            // old polygons are red
            actualPolyList.push_back(report::Plot_Polygon(poly, 1, "red", "solid"));
        }
        
        for (auto &poly : newPolygonList)
        {
            //new polygons are blue
            actualPolyList.push_back(report::Plot_Polygon(poly, 1, "blue", "dashed"));
        }
        report::Plot actualPlot(actualPolyList, "Actual Result");
        testReport.addPlot(actualPlot);

    }
    
    {
        ///Second test is merging two overlapping keep-in polygons that create a single keep-out "hole"
        //Basic shape: (not to scale
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
        
        //first polygon to merge
        VisiLibity::Polygon polygon1(std::vector<Point>{Point(3.0, 1.0), Point(3.0, 2.0), Point(1.0, 2.0), Point(1.0, 3.0), Point(3.0, 3.0), Point(3.0, 4.0), Point(0.0, 4.0), Point(0.0, 1.0)});
        //second polygon to merge
        VisiLibity::Polygon polygon2(std::vector<Point>{Point(2.0, 5.0), Point(4.0, 5.0), Point(4.0, 0.0), Point(2.0, 0.0)});
        
        //expected new polygon after merge
        VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(0.0, 1.0), Point(0.0, 4.0), Point(2.0, 4.0), Point(2.0, 5.0), Point(4.0, 5.0), Point(4.0, 00), Point(2.0, 0.0), Point(2.0, 1.0)});
        
        //expected keep-out "hole" created
        //CCW order
            VisiLibity::Polygon newPolygon2(std::vector<Point>{Point(1.0, 2.0), Point(2.0, 2.0), Point(2.0, 3.0), Point(1.0, 3.0)});
        
        
        //merge function arguments are vectors of polygons
        //expected function output polygon list
        std::vector<Polygon> expMergedPolygonList;
        expMergedPolygonList.push_back(newPolygon1);
        expMergedPolygonList.push_back(newPolygon2);
        
        //function input polygon list
        std::vector<VisiLibity::Polygon> oldPolygonList;
        oldPolygonList.push_back(polygon1);
        oldPolygonList.push_back(polygon2);
        
        //create resulting polygon list
        std::vector<VisiLibity::Polygon> newPolygonList;
        
        //test
        Polygon::union_(oldPolygonList,newPolygonList,epsilon);
        //compare actual to expected results
        EXPECT_TRUE(VisiLibity::equivalent(newPolygonList[0],expMergedPolygonList[0]));
        EXPECT_TRUE(VisiLibity::equivalent(newPolygonList[1], expMergedPolygonList[1]));
        //make sure there are no extraneous polygons in the list
        EXPECT_EQ(expMergedPolygonList.size(), newPolygonList.size());
        
        //Add to report
        testReport.addText("Test 2: Merging two overlapping polygons with hole in middle");
        
        //Expected Results
        std::vector<report::Plot_Polygon> expectedPolyList;
        for (auto &poly : oldPolygonList)
        {
            // old polygons are red
            expectedPolyList.push_back(report::Plot_Polygon(poly, 1, "red", "solid"));
        }
        
        for (auto &poly : expMergedPolygonList)
        {
            //new polygons are blue
            expectedPolyList.push_back(report::Plot_Polygon(poly, 1, "blue", "dashed"));
        }
        
        report::Plot expectedPlot(expectedPolyList, "Expected Result");
        testReport.addPlot(expectedPlot);
        
        //Actual Results
        std::vector<report::Plot_Polygon> actualPolyList;
        for (auto &poly : oldPolygonList)
        {
            // old polygons are red
            actualPolyList.push_back(report::Plot_Polygon(poly, 1, "red", "solid"));
        }
        
        for (auto &poly : newPolygonList)
        {
            //new polygons are blue
            actualPolyList.push_back(report::Plot_Polygon(poly, 1, "blue", "dashed"));
        }
        report::Plot actualPlot(actualPolyList, "Actual Result");
        testReport.addPlot(actualPlot);
        testReport.render();
        
        ///Third test is merging two overlapping keep-out polygons that create a single "hole" that is ignored because you can never reach it
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
    }
    ///Fourth test is merging polygons that are not adjacent and do not overlap. Distance is greater than epsilon
    // basic shape (not to scale):
    //              _______
    //             |       |
    //             |       |  _________
    //             |       | |         |
    //              -------  |         |
    //                       |         |
    //                       |_________|
    
    ///Fifth test is merging polygons that are not adjacent and do not overlap, however the distance is less than epsilon. The result is a merged polygon.s
    // basic shape (not to scale):
    //              _______
    //             |       |
    //             |       | _________
    //             |       ||         |
    //              ------- |         |
    //                      |         |
    //                      |_________|
};

int main(int argc, char **argv)
{
    // Build, Google Test run-time and environment tear-down
    ::testing::InitGoogleTest(&argc, argv);
    // Run the tests and return the results
    return RUN_ALL_TESTS();
}

