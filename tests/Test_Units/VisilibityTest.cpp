#include "gtest/gtest.h"

#include <boost/foreach.hpp>

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
    TestShape(std::vector<VisiLibity::Polygon> original, std::vector<VisiLibity::Polygon> expected)
    {
        m_originalPolygonList = original;
        m_expectedPolygonList = expected;
    };
    std::vector<VisiLibity::Polygon> m_originalPolygonList;
    std::vector<VisiLibity::Polygon> m_expectedPolygonList;
    static report::Report m_report_static;

    //define threshold - polygons within this distance of each other will be considered to be adjacent
    double m_epsilon = 0.05;
    void runTest(std::string description)
    {
        std::vector<VisiLibity::Polygon> actualPolygonList;
//        Polygon::union_(m_originalPolygonList,actualPolygonList,m_epsilon);
        Polygon::boost_union_(m_originalPolygonList,actualPolygonList,m_epsilon);

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
        m_report_static.addLine(description);

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
        m_report_static.addPlot(expectedPlot);

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
        m_report_static.addPlot(actualPlot);
    }
};

//TODO - add conversion test for boost polygons with holes
//TODO - CW test
//TODO - document classes
///TODO - standardize style
///TODO - doxygen
///TODO - standardize visilibity capitalization - see file name
///TODO - concave test
///TODO - handle epsilon
///TODO - multiple holes

TEST(VisiLibityTest, Polygon_union_overlapping)
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

    //first polygon to merge - CCW
    VisiLibity::Polygon polygon1(std::vector<Point>{Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 5.0), Point(0.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<Point>{Point(2.0, 0.0), Point(5.0, 0.0), Point(5.0, 3.0), Point(2.0, 3.0) });

    //expected new polygon after merge - CCW
    VisiLibity::Polygon newPolygon(std::vector<Point>{Point(3.0, 3.0), Point(3.0, 5.0), Point(0.0, 5.0), Point(0.0, 2.0), Point(2.0, 2.0), Point(2.0, 0.0), Point(5.0, 0.0), Point(5.0, 3.0)});

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    ts.runTest("Test 1: Merging two overlapping polygons");
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_basic_boost)
{
    //direct test of boost::union_
    //this test is just for my understanding of boost polygon, not to be kept as a permanent test
    //original code is straight out of boost union documentation, and I have dorked around with it trying to debug union not returning any polygons in other tests
    
    boost_polygon green, blue;
    std::vector<report::Plot_Polygon> plotList;
    
//    //second set of vertices is an inside ring/hole
    bg::read_wkt(
                              "POLYGON((2 1.3,2.4 1.7,2.8 1.8,3.4 1.2,3.7 1.6,3.4 2,4.1 3,5.3 2.6,5.4 1.2,4.9 0.8,2.9 0.7,2 1.3)"
                              "(4.0 2.0, 4.2 1.4, 4.8 1.9, 4.4 2.2, 4.0 2.0))", green);
// //polygon without hole
//        bg::read_wkt(
//                     "POLYGON((2 1.3,2.4 1.7,2.8 1.8,3.4 1.2,3.7 1.6,3.4 2,4.1 3,5.3 2.6,5.4 1.2,4.9 0.8,2.9 0.7,2 1.3))", green);
    plotList.push_back(report::Plot_Polygon(to_visiLibity(green), 1, "green", "solid", "thick"));
    
    bg::read_wkt(
                              "POLYGON((4.0 -0.5 , 3.5 1.0 , 2.0 1.5 , 3.5 2.0 , 4.0 3.5 , 4.5 2.0 , 6.0 1.5 , 4.5 1.0 , 4.0 -0.5))", blue);
    plotList.push_back(report::Plot_Polygon(to_visiLibity(blue), 1, "blue", "solid", "thick"));
    
    std::vector<boost_polygon> output;
    bg::union_(green, blue, output);
    if(output.size() > 0)
    {
        plotList.push_back(report::Plot_Polygon(to_visiLibity(output[0]), 1, "red", "dashed", "ultra thick"));
    }
    
    EXPECT_EQ(output.size(), 1);
    BOOST_FOREACH(boost_polygon const& p, output)
    {
        EXPECT_FLOAT_EQ(bg::area(p), 5.64795);
    }
    
    report::Plot plot(plotList, "Result");
    TestShape::m_report_static.addPlot(plot);
}

TEST(VisiLibityTest, Polygon_union_mine_boost)
{
    //direct test of boost::union_
    //this test is just for my understanding of boost polygon, not to be kept as a permanent test
    boost_polygon green, blue;
    std::vector<report::Plot_Polygon> plotList;
    
    bg::read_wkt(
                 "POLYGON((0.0 2.0, 3.0 2.0, 3.0 5.0, 0.0 5.0, 0.0 2.0))", green);
    plotList.push_back(report::Plot_Polygon(to_visiLibity(green), 1, "green", "solid", "thick"));
    
    bg::read_wkt(
                 "POLYGON((2.0 0.0, 2.0 3.0, 5.0 3.0, 5.0 0.0, 2.0 0.0))", blue);
    plotList.push_back(report::Plot_Polygon(to_visiLibity(blue), 1, "blue", "solid", "thick"));
 
    
    std::vector<boost_polygon> output;
    bg::union_(green, blue, output);
    if(output.size() > 0)
    {
        plotList.push_back(report::Plot_Polygon(to_visiLibity(output[0]), 1, "red", "dashed", "ultra thick"));
    }
    
    EXPECT_EQ(output.size(), 1);
    BOOST_FOREACH(boost_polygon const& p, output)
    {
        EXPECT_FLOAT_EQ(bg::area(p), 5.64795);
    }
    
    report::Plot plot(plotList, "Result");
    TestShape::m_report_static.addPlot(plot);
}

TEST(VisiLibityTest, Polygon_union_keepout_hole)
{
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

    //first polygon to merge - CCW
    VisiLibity::Polygon polygon1(std::vector<Point>{Point(3.0, 1.0), Point(3.0, 2.0), Point(1.0, 2.0), Point(1.0, 3.0), Point(3.0, 3.0), Point(3.0, 4.0), Point(0.0, 4.0), Point(0.0, 1.0)});
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<Point>{Point(2.0, 0.0), Point(4.0, 0.0),Point(4.0, 5.0),Point(2.0, 5.0)});

    //expected new polygon after merge - defined CW
    VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(0.0, 1.0), Point(0.0, 4.0), Point(2.0, 4.0), Point(2.0, 5.0), Point(4.0, 5.0), Point(4.0, 00), Point(2.0, 0.0), Point(2.0, 1.0)});
    //Make CCW
    newPolygon1.reverse();
    //expected keep-out "hole" created
    //CW order?
    VisiLibity::Polygon newPolygon2(std::vector<Point>{Point(1.0, 3.0), Point(2.0, 3.0), Point(2.0, 2.0), Point(1.0, 2.0)});

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);
    expPolygonList.push_back(newPolygon2);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    ts.runTest("Test 2: merging two overlapping keep-in polygons that create a single keep-out 'hole'");
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_keepin_hole)
{

//TODO: Implement TEST 3 iff we implement keep-in/keep-out based on CW/CCW polygon direction
    ///This test is merging two overlapping keep-out polygons that create a single "hole" that is ignored because you can never reach it
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

    //first polygon to merge - defined CCW
    VisiLibity::Polygon polygon1(std::vector<Point>{Point(3.0, 1.0), Point(3.0, 2.0), Point(1.0, 2.0), Point(1.0, 3.0), Point(3.0, 3.0), Point(3.0, 4.0), Point(0.0, 4.0), Point(0.0, 1.0)});
    //Make CW
    polygon1.reverse();
    //second polygon to merge - defined CCW
    VisiLibity::Polygon polygon2(std::vector<Point>{Point(2.0, 0.0), Point(4.0, 0.0),Point(4.0, 5.0),Point(2.0, 5.0)});
    //Make CW
    polygon2.reverse();

    //expected new polygon after merge - CCW
    VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(0.0, 1.0), Point(0.0, 4.0), Point(2.0, 4.0), Point(2.0, 5.0), Point(4.0, 5.0), Point(4.0, 00), Point(2.0, 0.0), Point(2.0, 1.0)});

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    ts.runTest("Test 3: Merging two overlapping polygons with hole in middle that will be ignored because it is unreachable");
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_nonadjacent)
{

    ///Third test is merging polygons that are not adjacent and do not overlap. Distance is greater than epsilon
    // basic shape (not to scale):
    //              _______
    //             |       |
    //             |       |  _________
    //             |       | |         |
    //              -------  |         |
    //                       |         |
    //                       |_________|

    //first polygon to merge - CCW
    VisiLibity::Polygon polygon1(std::vector<Point>{Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 5.0), Point(0.0, 5.0) });
    //second polygon to merge - CCW
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

    TestShape ts(originalPolygonList, expPolygonList);
    ts.runTest("Test 4: Attempt to merge two non-adjacent polygons");
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_near)
{
    ///Fourth test is merging polygons that are not adjacent and do not overlap, however the distance is less than epsilon. The result is a merged polygon.s
    // basic shape (not to scale):
    //              _______
    //             |       |
    //             |       | _________
    //             |       ||         |
    //              ------- |         |
    //                      |         |
    //                      |_________|

    //first polygon to merge - CCW
    VisiLibity::Polygon polygon1(std::vector<Point>{Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 5.0), Point(0.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<Point>{Point(3.04, 0.0), Point(6.0, 0.0), Point(6.0, 3.0), Point(3.04, 3.0) });

    //expected new polygon after merge - CCW
    VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(3.0, 3.0), Point(3.0, 5.0), Point(0.0, 5.0), Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 0.0), Point(6.0, 0.0), Point(6.0, 3.0)});

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    ts.runTest("Test 5: Merging two non-adjacent polygons that are within epsilon distance");
    TestShape::m_report_static.addLine("Polygon distance is " + std::to_string(boundary_distance( polygon1,polygon2 )));
    TestShape::m_report_static.addLine("Epsilon is " + std::to_string(ts.m_epsilon));
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_three)
{
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

    //first polygon to merge - CCW
    VisiLibity::Polygon polygon1(std::vector<Point>{Point(0.0, 2.0), Point(3.0, 2.0), Point(3.0, 5.0), Point(0.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<Point>{Point(2.0, 0.0), Point(5.0, 0.0), Point(5.0, 3.0), Point(2.0, 3.0) });
    //third polygon to merge - CCW
    VisiLibity::Polygon polygon3(std::vector<Point>{Point(1.0, 1.0), Point(4.0, 1.0), Point(4.0, 6.0), Point(1.0, 6.0)});


    //expected new polygon after merge - CCW
    VisiLibity::Polygon newPolygon1(std::vector<Point>{Point(0.0, 2.0), Point(0.0, 5.0), Point(1.0, 5.0), Point(1.0, 6.0), Point(4.0, 6.0), Point(4.0, 3.0), Point(5.0, 3.0), Point(5.0, 0.0), Point(2.0, 0.0), Point(2.0, 1.0), Point(1.0, 1.0), Point(1.0, 2.0)});
    //CCW
    newPolygon1.reverse();

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);
    originalPolygonList.push_back(polygon3);

    TestShape ts(originalPolygonList, expPolygonList);
    ts.runTest("Test 6: Merging three overlapping polygons");
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};


TEST(VisiLibityTest, Point_conversion)
{
    VisiLibity::Point visPoint(0,1);
    VisiLibity::boost_point b_point(0,1);

    //Visilibity Point to Boost point
    auto convertedBoostPoint = VisiLibity::to_boost(visPoint);
    EXPECT_TRUE(bg::equals(convertedBoostPoint, b_point));

    //Boost point to VisiLibity Point
    auto convertedVisPoint = VisiLibity::to_visiLibity(b_point);
    EXPECT_TRUE(VisiLibity::equivalent(visPoint, convertedVisPoint));
}
TEST(VisiLibityTest, Polygon_conversion)
{

    //Crete list of VisiLibity Points
    std::vector<Point> points({Point(2.0, 1.3), Point(4.1, 3.0), Point(5.3, 2.6),
        Point(2.9, 0.7), Point(2.0, 1.3)});
    //Create visilibity polygon
    VisiLibity::Polygon visPoly(points);


    //Create boost polygon
    boost_polygon boostPoly;

    //Append each point
    for (auto &point: points)
    {
        auto b_point = VisiLibity::to_boost(point);
        bg::append(boostPoly.outer(), b_point);
    }

    auto convertedVisPoly = VisiLibity::to_visiLibity(boostPoly);
    EXPECT_TRUE(VisiLibity::equivalent(convertedVisPoly, visPoly));

    auto convertedBoostPoly = VisiLibity::to_boost(visPoly);
    EXPECT_TRUE(boost::geometry::equals(boostPoly, convertedBoostPoly));

};

//Initialize static report
report::Report TestShape::m_report_static("VisiLibity");

int main(int argc, char **argv)
{
   
    // Build, Google Test run-time and environment tear-down
    ::testing::InitGoogleTest(&argc, argv);
    // Run the tests and return the results
    auto result = RUN_ALL_TESTS();
    TestShape::m_report_static.render();
    return result;
}
//
