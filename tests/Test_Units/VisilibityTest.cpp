// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/* 
 * File:   VisilibityTest.cpp
 * Author: Mandy Cinnamon
 *
 * Created on June 17, 2018, 2:34 PM
 *
 * 
 */
#include "gtest/gtest.h"

#include "boost/foreach.hpp"

#include "visilibity.h"
#include "TestReport.h"

/** \class TestShape
 * 
 * \par Description:
 * Helper class for VisiLibity polygon merge (boost_union) tests - takes original and expected lists of polygons,
 * performs the merge, then compares the output to the expected values and adds results to latex test report
 * 
 * \n
 */

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
    static test::report::Report m_report_static;

    //define threshold - polygons within this distance of each other will be considered to be adjacent
    double m_epsilon = 0.05;
    bool runTest(std::string description)
    {
        std::vector<VisiLibity::Polygon> actualPolygonList;
        // VisiLibity::Polygon::union_(m_originalPolygonList,actualPolygonList,m_epsilon);
        auto success = VisiLibity::Polygon::boost_union(m_originalPolygonList,actualPolygonList,m_epsilon);

        //make sure there are no extraneous polygons in the list
        EXPECT_EQ(m_expectedPolygonList.size(), actualPolygonList.size());

        //get length of shorter of two polygon lists, in case above check fails
        int n_toCompare = (std::min)(m_expectedPolygonList.size(), actualPolygonList.size());
        //compare actual to expected results for each polygon
        for (int polyIdx = 0; polyIdx < n_toCompare; polyIdx++)
        {
            EXPECT_TRUE(VisiLibity::equivalent(actualPolygonList[polyIdx], m_expectedPolygonList[polyIdx], m_epsilon));
        }

        //Add to report
        m_report_static.addLine(description);

        //Expected Results
        std::vector<test::report::PlotPolygon> expectedPolyList;
        for (auto &poly : m_originalPolygonList)
        {
            // old polygons are red
            expectedPolyList.push_back(test::report::PlotPolygon(poly, 1, "red", "solid", "thick"));
        }

        for (auto &poly : m_expectedPolygonList)
        {
            //new polygons are blue
            expectedPolyList.push_back(test::report::PlotPolygon(poly, 1, "blue", "dashed", "ultra thick"));
        }

        test::report::Plot expectedPlot(expectedPolyList, "Expected Result");
        m_report_static.addPlot(expectedPlot);

        //Actual Results
        std::vector<test::report::PlotPolygon> actualPolyList;
        for (auto &poly : m_originalPolygonList)
        {
            // old polygons are red
            actualPolyList.push_back(test::report::PlotPolygon(poly, 1, "red", "solid", "thick"));
        }

        for (auto &poly : actualPolygonList)
        {
            //new polygons are blue
            actualPolyList.push_back(test::report::PlotPolygon(poly, 1, "blue", "dashed", "ultra thick"));
        }
        test::report::Plot actualPlot(actualPolyList, "Actual Result");
        m_report_static.addPlot(actualPlot);
        return success;
    }

};

//TODO - document classes
///TODO - standardize style
///TODO - doxygen
///TODO - standardize visilibity capitalization - see file name

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
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(2.0, 0.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(5.0, 3.0), VisiLibity::Point(2.0, 3.0) });

    //expected new polygon after merge - CCW
    VisiLibity::Polygon newPolygon(std::vector<VisiLibity::Point>{VisiLibity::Point(3.0, 3.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0), VisiLibity::Point(0.0, 2.0), VisiLibity::Point(2.0, 2.0), VisiLibity::Point(2.0, 0.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(5.0, 3.0)});

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<VisiLibity::Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    auto success = ts.runTest("Merging two overlapping polygons");
    EXPECT_TRUE(success);

    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_tangent)
{
    /// Two polygons that share a single vertex but are not overlapping or adjacent
    // basic shape (not to scale):
    //              _______
    //             |       |
    //             |       |
    //              ------- ---------
    //                     |         |
    //                     |_________|
    
    //first polygon to merge - CCW
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(3.0, 0.0), VisiLibity::Point(6.0, 0.0), VisiLibity::Point(6.0, 2.0), VisiLibity::Point(3.0, 2.0) });
    
    //expected new polygon after merge - CCW
    VisiLibity::Polygon newPolygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0) });
    VisiLibity::Polygon newPolygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(3.0, 0.0), VisiLibity::Point(6.0, 0.0), VisiLibity::Point(6.0, 2.0), VisiLibity::Point(3.0, 2.0) });

    
    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<VisiLibity::Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);
    expPolygonList.push_back(newPolygon2);
    
    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);
    
    TestShape ts(originalPolygonList, expPolygonList);
    auto success = ts.runTest("Attempt to merge two tangent polygons (non-adjacent)");
    EXPECT_TRUE(success);
    
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

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
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(3.0, 1.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(1.0, 2.0), VisiLibity::Point(1.0, 3.0), VisiLibity::Point(3.0, 3.0), VisiLibity::Point(3.0, 4.0), VisiLibity::Point(0.0, 4.0), VisiLibity::Point(0.0, 1.0)});
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(2.0, 0.0), VisiLibity::Point(4.0, 0.0), VisiLibity::Point(4.0, 5.0), VisiLibity::Point(2.0, 5.0)});

    //expected new polygon after merge - defined CW
    VisiLibity::Polygon newPolygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 1.0), VisiLibity::Point(0.0, 4.0), VisiLibity::Point(2.0, 4.0), VisiLibity::Point(2.0, 5.0), VisiLibity::Point(4.0, 5.0), VisiLibity::Point(4.0, 00), VisiLibity::Point(2.0, 0.0), VisiLibity::Point(2.0, 1.0)});
    //Make CCW
    newPolygon1.reverse();
    //expected keep-out "hole" created
    //CW order?
    VisiLibity::Polygon newPolygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(1.0, 3.0), VisiLibity::Point(2.0, 3.0), VisiLibity::Point(2.0, 2.0), VisiLibity::Point(1.0, 2.0)});

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<VisiLibity::Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);
    expPolygonList.push_back(newPolygon2);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    auto success = ts.runTest("Merging two overlapping keep-in polygons that create a single keep-out 'hole'");
    EXPECT_TRUE(success);
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_multiple_holes)
{
    ///Second test is merging two overlapping keep-in polygons that create a single keep-out "hole"
    //Basic shape: (not to scale)
    //          _____
    //         |      |
    //         |      |
    //  _______|__   _|________
    // |          | | |        |
    // |          | | |        |
    // |      ____| |_|_____   |
    // |     | |      |     |  |
    // |     | |      |     |  |
    // |     | |      |     |  |
    // |     |_|__   _|_____|  |
    // |          | | |        |
    // |          | | |        |
    // |          | | |        |
    // |__________| |_|________|
    //         |______|
    //

    //first polygon to merge - CCW
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(3.0, 1.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(1.0, 2.0), VisiLibity::Point(1.0, 3.0), VisiLibity::Point(3.0, 3.0), VisiLibity::Point(3.0, 4.0), VisiLibity::Point(0.0, 4.0), VisiLibity::Point(0.0, 1.0)});
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(2.0, 0.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(5.0, 5.0), VisiLibity::Point(2.0, 5.0)});
    //first polygon to merge - CCW
    VisiLibity::Polygon polygon3(std::vector<VisiLibity::Point>{VisiLibity::Point(4.0, 1.0), VisiLibity::Point(7.0, 1.0), VisiLibity::Point(7.0, 4.0), VisiLibity::Point(4.0, 4.0), VisiLibity::Point(4.0, 3.0), VisiLibity::Point(6.0, 3.0), VisiLibity::Point(6.0, 2.0), VisiLibity::Point(4.0, 2.0)});

    //expected new polygon after merge - defined CW
    VisiLibity::Polygon newPolygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 1.0), VisiLibity::Point(0.0, 4.0), VisiLibity::Point(2.0, 4.0), VisiLibity::Point(2.0, 5.0), VisiLibity::Point(5.0, 5.0), VisiLibity::Point(5.0, 4.0), VisiLibity::Point(7.0, 4.0), VisiLibity::Point(7.0, 1.0), VisiLibity::Point(5.0, 1.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(2.0, 0.0), VisiLibity::Point(2.0, 1.0)});
    //Make CCW
    newPolygon1.reverse();
    //expected keep-out "hole" created
    //CW order?
    VisiLibity::Polygon newPolygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(5.0, 2.0), VisiLibity::Point(5.0, 3.0), VisiLibity::Point(6.0, 3.0), VisiLibity::Point(6.0, 2.0)});

    VisiLibity::Polygon newPolygon3(std::vector<VisiLibity::Point>{VisiLibity::Point(1.0, 3.0), VisiLibity::Point(2.0, 3.0), VisiLibity::Point(2.0, 2.0), VisiLibity::Point(1.0, 2.0)});

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<VisiLibity::Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);
    expPolygonList.push_back(newPolygon2);
    expPolygonList.push_back(newPolygon3);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);
    originalPolygonList.push_back(polygon3);

    TestShape ts(originalPolygonList, expPolygonList);
    auto success = ts.runTest("Merging three overlapping keep-in polygons that create multiple keep-out 'holes'");
    EXPECT_TRUE(success);
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_invalid_polygon)
{
//
   // basic shape (not to scale):
    //                     |
    //                     |
    //                    _|_______
    //                   | |       |
    //                   |         |
    //                   |         |
    //                   |_________|

    //first polygon to merge - CCW
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(2.0, 0.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(5.0, 3.0), VisiLibity::Point(2.0, 3.0) });

    VisiLibity::Polygon newPolygon(std::vector<VisiLibity::Point>{VisiLibity::Point(2.0, 0.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(5.0, 3.0), VisiLibity::Point(2.0, 3.0) });
  
    //merge function arguments are vectors of polygons
    std::vector<VisiLibity::Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon);


    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    auto success = ts.runTest("Merging valid polygon with invalid polygon that has less than 3 vertices");
    //should return false because wrong orientation
    EXPECT_FALSE(success);
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_invalid_orientation)
{
//Attempt to merge invalid polygon with less than three vertices 
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
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(3.0, 1.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(1.0, 2.0), VisiLibity::Point(1.0, 3.0), VisiLibity::Point(3.0, 3.0), VisiLibity::Point(3.0, 4.0), VisiLibity::Point(0.0, 4.0), VisiLibity::Point(0.0, 1.0)});
    //Make CW
    polygon1.reverse();
    //second polygon to merge - defined CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(2.0, 0.0), VisiLibity::Point(4.0, 0.0), VisiLibity::Point(4.0, 5.0), VisiLibity::Point(2.0, 5.0)});
    //Make CW
    polygon2.reverse();


    //merge function arguments are vectors of polygons
    //expected function output empty polygon list
    std::vector<VisiLibity::Polygon> expPolygonList;

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    auto success = ts.runTest("Merging two polygons that are invalid due to orientation");
    //should return false because wrong orientation
    EXPECT_FALSE(success);
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
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(4, 0.0), VisiLibity::Point(7, 0.0), VisiLibity::Point(7, 3.0), VisiLibity::Point(4, 3.0) });

    //expected new polygons after merge - both unchanged from original
    VisiLibity::Polygon newPolygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0) });
    VisiLibity::Polygon newPolygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(4, 0.0), VisiLibity::Point(7, 0.0), VisiLibity::Point(7, 3.0), VisiLibity::Point(4, 3.0) });

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<VisiLibity::Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);
    expPolygonList.push_back(newPolygon2);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    auto success = ts.runTest("Attempt to merge two non-adjacent polygons");
    EXPECT_TRUE(success);
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
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(3.04, 0.0), VisiLibity::Point(6.0, 0.0), VisiLibity::Point(6.0, 3.0), VisiLibity::Point(3.04, 3.0) });

    //expected new polygon after merge - CCW
    VisiLibity::Polygon newPolygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(3.0, 3.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0), VisiLibity::Point(0.0, 2.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 0.0), VisiLibity::Point(6.0, 0.0), VisiLibity::Point(6.0, 3.0)});

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<VisiLibity::Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);

    TestShape ts(originalPolygonList, expPolygonList);
    ts.runTest("Merging two non-adjacent polygons that are within epsilon distance");
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

TEST(VisiLibityTest, Polygon_union_three_overlapping)
{
    ///Fifth test is merging 3 overlapping polygons
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
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(2.0, 0.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(5.0, 3.0), VisiLibity::Point(2.0, 3.0) });
    //third polygon to merge - CCW
    VisiLibity::Polygon polygon3(std::vector<VisiLibity::Point>{VisiLibity::Point(1.0, 1.0), VisiLibity::Point(4.0, 1.0), VisiLibity::Point(4.0, 6.0), VisiLibity::Point(1.0, 6.0)});


    //expected new polygon after merge - CCW
    VisiLibity::Polygon newPolygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(0.0, 5.0), VisiLibity::Point(1.0, 5.0), VisiLibity::Point(1.0, 6.0), VisiLibity::Point(4.0, 6.0), VisiLibity::Point(4.0, 3.0), VisiLibity::Point(5.0, 3.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(2.0, 0.0), VisiLibity::Point(2.0, 1.0), VisiLibity::Point(1.0, 1.0), VisiLibity::Point(1.0, 2.0)});
    //CCW
    newPolygon1.reverse();

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<VisiLibity::Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);
    originalPolygonList.push_back(polygon3);

    TestShape ts(originalPolygonList, expPolygonList);
    auto success = ts.runTest("Merging three mutually overlapping polygons");
    EXPECT_TRUE(success);
    if(Test::HasNonfatalFailure())
    {
        TestShape::m_report_static.addLine("Test Fails", "red");
    }
    else
    {
        TestShape::m_report_static.addLine("Test Passes", "green");
    }
};

TEST(VisiLibityTest, Polygon_union_three_nonoverlapping)
{
    ///Fifth test is merging 3 polygons, where two do not overlap each other
    // basic shape (not to scale):
    //                  ______
    //              ___|___   |
    //             |   |   |  |
    //             |   |   | _|____
    //             |   |   || |    |
    //              ------- | |    |
    //                 |____|_|    |
    //                      |______|

    //first polygon to merge - CCW
    VisiLibity::Polygon polygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(3.0, 2.0), VisiLibity::Point(3.0, 5.0), VisiLibity::Point(0.0, 5.0) });
    //second polygon to merge - CCW
    VisiLibity::Polygon polygon2(std::vector<VisiLibity::Point>{VisiLibity::Point(3.5, 0.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(5.0, 3.0), VisiLibity::Point(3.5, 3.0) });
    //third polygon to merge - CCW
    VisiLibity::Polygon polygon3(std::vector<VisiLibity::Point>{VisiLibity::Point(1.0, 1.0), VisiLibity::Point(4.0, 1.0), VisiLibity::Point(4.0, 6.0), VisiLibity::Point(1.0, 6.0)});


    //expected new polygon after merge - CCW
    VisiLibity::Polygon newPolygon1(std::vector<VisiLibity::Point>{VisiLibity::Point(0.0, 2.0), VisiLibity::Point(0.0, 5.0), VisiLibity::Point(1.0, 5.0), VisiLibity::Point(1.0, 6.0), VisiLibity::Point(4.0, 6.0), VisiLibity::Point(4.0, 3.0), VisiLibity::Point(5.0, 3.0), VisiLibity::Point(5.0, 0.0), VisiLibity::Point(3.5, 0.0), VisiLibity::Point(3.5, 1.0), VisiLibity::Point(1.0, 1.0), VisiLibity::Point(1.0, 2.0)});
    //CCW
    newPolygon1.reverse();

    //merge function arguments are vectors of polygons
    //expected function output polygon list
    std::vector<VisiLibity::Polygon> expPolygonList;
    expPolygonList.push_back(newPolygon1);

    //function input polygon list
    std::vector<VisiLibity::Polygon> originalPolygonList;
    originalPolygonList.push_back(polygon1);
    originalPolygonList.push_back(polygon2);
    originalPolygonList.push_back(polygon3);

    TestShape ts(originalPolygonList, expPolygonList);
    auto success = ts.runTest("Merging three non-mutually overlapping polygons");
    EXPECT_TRUE(success);
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
    EXPECT_TRUE(boost::geometry::equals(convertedBoostPoint, b_point));

    //Boost point to VisiLibity Point
    auto convertedVisPoint = VisiLibity::to_visiLibity(b_point);
    EXPECT_TRUE(VisiLibity::equivalent(visPoint, convertedVisPoint));
}

TEST(VisiLibityTest, Polygon_conversion)
{

    //Create CCW list of VisiLibity Points
    std::vector<VisiLibity::Point> points({ VisiLibity::Point(0.0, 0.0), VisiLibity::Point(1.0, 0.0), VisiLibity::Point(1.0, 1.0),
		VisiLibity::Point(0.0, 1.0)});
    //Create a polygon with visilibity points
	VisiLibity::Polygon visPoly(points);
    //put that polygon into a vector of length 1
    std::vector<VisiLibity::Polygon> visPolyList(1,visPoly);

    //Create boost polygon
	VisiLibity::boost_polygon boostPoly;

    //Append each point
    for (auto &point: points)
    {
        //convert visiLibity point to boost point
        auto b_point = VisiLibity::to_boost(point);
        //append to boost Polygon
        boost::geometry::append(boostPoly.outer(), b_point);
    }

    //convert boost polygon to visiLibity polygon list
    auto convertedVisPolyList = VisiLibity::to_visiLibity(boostPoly);

    //check size of resulting converted polygon list
    EXPECT_EQ(convertedVisPolyList.size(), visPolyList.size());

    //if converted polygon list has the same size as original list, check each polygon (should only be 1)
    if(convertedVisPolyList.size() == visPolyList.size())
    {
        //compare each converted visiLibity polygon to the original polygon
        for (int polyIdx = 0; polyIdx < convertedVisPolyList.size(); polyIdx++)
        {
            EXPECT_TRUE(VisiLibity::equivalent(convertedVisPolyList[polyIdx], visPolyList[polyIdx]));
        }
    }

    //check size of resulting converted polygon list
    EXPECT_EQ(convertedVisPolyList.size(), visPolyList.size());

    //convert visiLibity polygon to boost polygon
    auto convertedBoostPoly = VisiLibity::to_boost(std::vector<VisiLibity::Polygon>(1,visPoly));

    EXPECT_TRUE(boost::geometry::equals(convertedBoostPoly, boostPoly));
};

TEST(VisiLibityTest, Polygon_conversion_with_holes)
{

    //Create CCW list of VisiLibity Points
    std::vector<VisiLibity::Point> outer_points({ VisiLibity::Point(0.0, 0.0), VisiLibity::Point(4.0, 0.0), VisiLibity::Point(4.0, 4.0),
		VisiLibity::Point(0.0, 4.0)});
    //Create a polygon with visilibity points
	VisiLibity::Polygon visPoly(outer_points);
    //put that polygon into a vector of length 1
    std::vector<VisiLibity::Polygon> visPolyList(1,visPoly);

    //Create CW list of VisiLibity Points for hole
    std::vector<VisiLibity::Point> inner_points({ VisiLibity::Point(2.0, 2.0), VisiLibity::Point(2.0, 3.0), VisiLibity::Point(3.0, 3.0),
		VisiLibity::Point(3.0, 2.0)});
    //Create polygon to represent hole
	VisiLibity::Polygon hole(inner_points);
    //add hole to list
    visPolyList.push_back(hole);

    //Create boost polygon
	VisiLibity::boost_polygon boostPoly{{{0.0, 0.0}, {4.0, 0.0}, {4.0, 4.0}, {0.0, 4.0}},
        {{2.0, 2.0}, {2.0, 3.0}, {3.0, 3.0}, {3.0, 2.0}}};

    //convert boost polygon to visiLibity polygon list
    auto convertedVisPolyList = VisiLibity::to_visiLibity(boostPoly);

    //check size of resulting converted polygon list
    EXPECT_EQ(convertedVisPolyList.size(), visPolyList.size());

    //if converted polygon list has the same size as original list, check each polygon (should only be 1)
    if(convertedVisPolyList.size() == visPolyList.size())
    {
        //compare each converted visiLibity polygon to the original polygon
        for (int polyIdx = 0; polyIdx < convertedVisPolyList.size(); polyIdx++)
        {
            EXPECT_TRUE(VisiLibity::equivalent(convertedVisPolyList[polyIdx], visPolyList[polyIdx]));
        }
    }
    //check size of resulting converted polygon list
    EXPECT_EQ(convertedVisPolyList.size(), visPolyList.size());

    //convert visiLibity polygon to boost polygon
    auto convertedBoostPoly = VisiLibity::to_boost(visPolyList);
    auto actual = VisiLibity::to_visiLibity(convertedBoostPoly);
    auto expected = VisiLibity::to_visiLibity(boostPoly);
    EXPECT_TRUE(boost::geometry::equals(convertedBoostPoly, boostPoly));
};

TEST(VisiLibityTest, OffsetPolygon)
{
    //geometries from boost documentation at https://www.boost.org/doc/libs/1_58_0/libs/geometry/doc/html/geometry/reference/algorithms/union_.html
    std::vector<VisiLibity::Polygon> polygonList, resultingPolygons;
    double epsilon = 0.5;
    double delta = 1.0;
	VisiLibity::boost_polygon green, blue;
    
    boost::geometry::read_wkt("POLYGON((2 1.3,2.4 1.7,2.8 1.8,3.4 1.2,3.7 1.6,3.4 2,4.1 3,5.3 2.6,5.4 1.2,4.9 0.8,2.9 0.7,2 1.3))", green);
    //make this polygon CCW
    boost::geometry::correct(green);
    auto visPolyList = VisiLibity::to_visiLibity(green);
    if(visPolyList.size() == 1)
    {
        polygonList.push_back(visPolyList[0]);
    }
    boost::geometry::read_wkt("POLYGON((4.0 -0.5 , 3.5 1.0 , 2.0 1.5 , 3.5 2.0 , 4.0 3.5 , 4.5 2.0 , 6.0 1.5 , 4.5 1.0 , 4.0 -0.5))", blue);
    //make this polygon CCW
    boost::geometry::correct(blue);
    visPolyList = VisiLibity::to_visiLibity(blue);
    if(visPolyList.size() == 1)
    {
        polygonList.push_back(visPolyList[0]);
    }
    
    //Create CCW list of VisiLibity Points
    std::vector<VisiLibity::Point> outer_points(
        {
		   VisiLibity::Point(4.72076, 4.5),
		   VisiLibity::Point(3.27924, 4.5),
		   VisiLibity::Point(3.13037, 4.0534),
		   VisiLibity::Point(2.84413, 3.21719),
		   VisiLibity::Point(2.3788, 2.76711),
		   VisiLibity::Point(2.1766, 2.68088),
		   VisiLibity::Point(1.91493, 2.60951),
		   VisiLibity::Point(1.92993, 2.5757),
		   VisiLibity::Point(1.90556, 2.56531),
		   VisiLibity::Point(1.86967, 2.58388),
		   VisiLibity::Point(1.81062, 2.52483),
		   VisiLibity::Point(1.4466, 2.36963),
		   VisiLibity::Point(1.4988, 2.21302),
		   VisiLibity::Point(1.37686, 2.09107),
		   VisiLibity::Point(1, 2.22076),
		   VisiLibity::Point(1, 1.71421),
           VisiLibity::Point(0.95823, 1.67244),
           VisiLibity::Point(1, 1.25061),
           VisiLibity::Point(1, 0.779241),
           VisiLibity::Point(1.04827, 0.763151),
           VisiLibity::Point(1.0515, 0.730481),
           VisiLibity::Point(1.23729, 0.606625),
           VisiLibity::Point(2.3453, -0.132052),
           VisiLibity::Point(3.05592, -0.660412),
           VisiLibity::Point(3.13037, -1.0534),
           VisiLibity::Point(3.30244, -0.996042),
           VisiLibity::Point(3.27924, -1.5),
           VisiLibity::Point(4.72076, -1.5),
           VisiLibity::Point(4.94868, -0.816228),
           VisiLibity::Point(5.15798, -0.188351),
           VisiLibity::Point(5.2725, -0.182624),
           VisiLibity::Point(5.32949, -0.137036),
           VisiLibity::Point(6.16847, 0.502063),
           VisiLibity::Point(6.5534, 0.630374),
           VisiLibity::Point(6.54377, 0.659248),
           VisiLibity::Point(7, 0.779241),
           VisiLibity::Point(7, 2.22076),
           VisiLibity::Point(6.5534, 2.36963),
           VisiLibity::Point(6.55339, 2.36963),
           VisiLibity::Point(6.31623, 2.44868),
           VisiLibity::Point(6.27585, 2.97373),
           VisiLibity::Point(5.90391, 3.45279),
           VisiLibity::Point(5.61623, 3.54868),
           VisiLibity::Point(5.61623, 3.54868),
           VisiLibity::Point(4.89503, 3.78908),
           VisiLibity::Point(4.89445, 3.79502),
           VisiLibity::Point(4.94868, 3.81623),
           VisiLibity::Point(4.86963, 4.0534),
           VisiLibity::Point(4.86963, 4.0534),
        });
    //Create a polygon with visilibity points
	VisiLibity::Polygon visPoly(outer_points);
    //put that polygon into a vector of length 1
    std::vector<VisiLibity::Polygon> expectedVisPolyList(1,visPoly);
    
    EXPECT_TRUE(VisiLibity::Polygon::offset_polygons(polygonList, resultingPolygons, delta, epsilon));
    auto resultSize = resultingPolygons.size();
    EXPECT_EQ(1, resultSize);
    if(resultSize == 1)
    {
        EXPECT_TRUE(VisiLibity::equivalent(resultingPolygons[0], expectedVisPolyList[0], epsilon));
    }
    
    //Add to report
    TestShape::m_report_static.addLine(std::string("Test of offset polygon function"));
    
    //Expected Results
    std::vector<test::report::PlotPolygon> expectedPolyList;
    for (auto &poly : polygonList)
    {
        // old polygons are red
        expectedPolyList.push_back(test::report::PlotPolygon(poly, 1, "red", "solid", "thick"));
    }
    
    for (auto &poly : expectedVisPolyList)
    {
        //new polygons are blue
        expectedPolyList.push_back(test::report::PlotPolygon(poly, 1, "blue", "dashed", "ultra thick"));
    }
    test::report::Plot expectedPlot(expectedPolyList, "Expected Result");
    TestShape::m_report_static.addPlot(expectedPlot);
    
    //Actual Results
    std::vector<test::report::PlotPolygon> actualPolyList;
    for (auto &poly : polygonList)
    {
        // old polygons are red
        actualPolyList.push_back(test::report::PlotPolygon(poly, 1, "red", "solid", "thick"));
    }
    
    for (auto &poly : resultingPolygons)
    {
        //new polygons are blue
        actualPolyList.push_back(test::report::PlotPolygon(poly, 1, "blue", "dashed", "ultra thick"));
    }
    test::report::Plot actualPlot(actualPolyList, "Actual Result");
    TestShape::m_report_static.addPlot(actualPlot);
}

//Initialize static report
test::report::Report TestShape::m_report_static("VisiLibity");

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
