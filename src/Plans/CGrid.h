// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

//
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION IS RELEASED "AS IS." THE
//    U.S.GOVERNMENT MAKES NO WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, CONCERNING
//    THIS SOFTWARE AND ANY ACCOMPANYING DOCUMENTATION, INCLUDING, WITHOUT LIMITATION,
//    ANY WARRANTIES OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT
//    WILL THE U.S. GOVERNMENT BE LIABLE FOR ANY DAMAGES, INCLUDING ANY LOST PROFITS,
//    LOST SAVINGS OR OTHER INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE,
//    OR INABILITY TO USE, THIS SOFTWARE OR ANY ACCOMPANYING DOCUMENTATION, EVEN IF
//    INFORMED IN ADVANCE OF THE POSSIBILITY OF SUCH DAMAGES.
//
// CPolygon.h: interface for the CPolygon class.
//
//////////////////////////////////////////////////////////////////////
//    Date    Name    Ver     Modification
//    3/4/05    afj     1.0     created
//
//////////////////////////////////////////////////////////////////////


#if !defined(GRID_HEADER)
#define GRID_HEADER

// apparently only diskreads the header file once. 
#if _MSC_VER > 1000
#pragma once
#endif // end if 

/****************************************************
*                    Includes                        *
*****************************************************/
#include <vector>
#include <string>
//#include "GlobalDefines.h"    //V_INT_t, V_POSITION_t
using namespace std;
#include "Position.h"

/* test if a & b are within epsilon.  Favors cases where a < b */
#define Near(a,b,eps)    ( ((b)-(eps)<(a)) && ((a)-(eps)<(b)) )

namespace n_FrameworkLib
{

class CGrid
{
/*************************************************
*                Private Member Variables         *
*************************************************/
private:
    struct CellData{ 
        double xa,ya; 
        double minx, maxx, miny, maxy;
        double ax,ay; 
        double slope; 
        double inv_slope; 
        CPosition VertexA;
        CPosition VertexB;
    };    //Only create if needed...
    
    typedef vector<CellData> VData;
    typedef vector<CellData>::iterator VDataIterator;
    
    VDataIterator DIndex;
    VDataIterator DUpperBound;
    
    struct Cell{ 
        Cell():gc_flags(0),tot_edges(0),Data(0){};
        unsigned short gc_flags;        
        short tot_edges;
        VData *Data ;                            // make pointer because doesn't always exist
    };    // always create 
    
    typedef vector<Cell> VCell;
    typedef vector<Cell>::iterator VCellIterator;
    
    VCell VGrid;
    VCellIterator    Index;
    VCellIterator    UpperBound;
    
//    CPolygon::VPoints Polygon_Points;
    
    double *glx, *gly;                                        // change to vector - grid x & y coordinates
    double xdelta, ydelta, inv_xdelta, inv_ydelta;
    int XGridResolution, YGridResolution, TotalCells;        // grid size
    
    // Grid constants
    const double NearEpsilon;
    const double dHUGE;
    const unsigned short GC_BL_IN;    //    0x0001;    /* bottom left corner is in (else out) */
    const unsigned short GC_BR_IN;    //    0x0002;    /* bottom right corner is in (else out) */
    const unsigned short GC_TL_IN;    //    0x0004;    /* top left corner is in (else out) */
    const unsigned short GC_TR_IN;    //    0x0008;    /* top right corner is in (else out) */
    const unsigned short GC_L_EDGE_HIT;    //    0x0010;    /* left edge is crossed */
    const unsigned short GC_R_EDGE_HIT;    //    0x0020;    /* right edge is crossed */
    const unsigned short GC_B_EDGE_HIT;    //    0x0040;    /* bottom edge is crossed */
    const unsigned short GC_T_EDGE_HIT;    //    0x0080;    /* top edge is crossed */
    const unsigned short GC_B_EDGE_PARITY;    //    0x0100;    /* bottom edge parity */
    const unsigned short GC_T_EDGE_PARITY;    //    0x0200;    /* top edge parity */
    const unsigned short GC_AIM_L;    //    (0<<10); /* aim towards left edge */
    const unsigned short GC_AIM_B;    //    (1<<10); /* aim towards bottom edge */
    const unsigned short GC_AIM_R;    //    (2<<10); /* aim towards right edge */
    const unsigned short GC_AIM_T;    //    (3<<10); /* aim towards top edge */
    const unsigned short GC_AIM_C;    //    (4<<10); /* aim towards a corner */
    const unsigned short GC_AIM;    //     0x1c00;
    
    const unsigned short GC_L_EDGE_CLEAR;    // GC_L_EDGE_HIT;
    const unsigned short GC_R_EDGE_CLEAR;    // GC_R_EDGE_HIT;
    const unsigned short GC_B_EDGE_CLEAR;    // GC_B_EDGE_HIT;
    const unsigned short GC_T_EDGE_CLEAR;    // GC_T_EDGE_HIT;
    
#define GC_ALL_EDGE_CLEAR    (GC_L_EDGE_HIT |  GC_R_EDGE_HIT |  \
    GC_B_EDGE_HIT |  GC_T_EDGE_HIT )
    
                                            /************************************************
                                            *                Private Member Functions        *
    *************************************************/
private:
    
    void Setup_Corner_Value(stringstream &sstrErrorMessage);
    
    bool Setup_GridData(Cell &Cur_Cell, double xa, double ya, double xb, double yb, 
        CPosition &vtxa, CPosition &vtxb, stringstream &sstrErrorMessage);
    
    void Print();
    
    // copy constructor - make unusable to prevent bad things from happening
    CGrid(const CGrid& grid);
    // assignment operator - make unusable to prevent bad things from happening
    CGrid & operator = (const CGrid& grid) = delete;
    
    
    /************************************************
    *                Public Member Functions         *
    *************************************************/
public: 
    // default constructor
    CGrid(std::vector<int32_t>& viVerticies,V_POSITION_t& vposVertexContainer, int x_grid_resolution, 
        int y_grid_resolution, CPosition &min, CPosition &max,
        stringstream &sstrErrorMessage );
    
    ~CGrid();                                                //Destructor
    
    bool InPolygon(double x, double y, double z, const CPosition &min, stringstream &sstrErrorMessage);
    
    };

        
};      //namespace n_FrameworkLib


#endif // !defined(POLYGON_HEADER)
