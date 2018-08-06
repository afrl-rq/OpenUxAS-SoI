// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
//
// Copyright (c) 2018 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

/*
 * File:   TestReport.h
 * Author: Amanda Cinnamon
 *
 * Created on Jun 12, 2018, 15:17 PM
 */

#ifndef UXAS_TEST_REPORT_H
#define UXAS_TEST_REPORT_H

#include <stdio.h>
#include "visilibity.h"

namespace test
{
namespace report
{
/** \class PlotElement
* 
* \par Description:
* base class for report plotting elements, contains info about how the plot will be rendered
* 
* \n
*/
class PlotElement
{
public:
    PlotElement();
    ///TODO: should these be public or private
    std::string m_color;
    std::string m_lineStyle;
    ///TODO: should this be float, double, int?
    std::string m_thickness;
    int m_arrow;
};
/** \class PlotLine
* 
* \par Description:
* line to be plotted
* 
* \n
*/
class PlotLine: public PlotElement
{
    PlotLine();
    VisiLibity::Line_Segment m_line;
};
/** \class PlotPolygon
* 
* \par Description:
* Polygon to be plotted
* 
* \n
*/
class PlotPolygon: public PlotElement
{
public:
    PlotPolygon();
    PlotPolygon(VisiLibity::Polygon x);
    PlotPolygon(VisiLibity::Polygon polygon, int arrow, std::string color, std::string lineStyle, std::string thickness);
    bool addPoint(VisiLibity::Point x);
    std::vector<VisiLibity::Point> m_points;
    VisiLibity::Polygon m_polygon;
};
/** \class PlotLine
* 
* \par Description:
* Plot for LaTEX report
* 
* \n
*/
class Plot
{
public:
    Plot();
    Plot(std::vector<VisiLibity::Point> x);
    Plot(std::vector<PlotLine> x);
    Plot(std::vector<PlotPolygon> polygonList, std::string caption);
    bool addPoint(VisiLibity::Point x);
    bool addLine(PlotLine x);
    bool addPolygon(PlotPolygon x);
    std::vector<VisiLibity::Point> m_points;
    std::vector<PlotLine> m_lines;
    std::vector<PlotPolygon> m_polygons;
    std::string m_caption;
};

/*! class Report
 * \brief Creates a LaTEX report of test results
 * Parameters
 *
 *
 */
class Report
{
public:
    Report();
    Report(std::string x);
    /** \brief Name of test to be reported*/
    std::string m_testName;

    ///TODO: should I be passing by reference?
    bool addPlot(Plot x);
    bool close();
    bool render();
    void addText(std::string x);
    void addLine(std::string x);
    void addLine(std::string content, std::string color);

    std::vector<Plot> m_plots;
    std::string m_content;
};
}
}
#endif /* UXAS_TEST_REPORT_H */
