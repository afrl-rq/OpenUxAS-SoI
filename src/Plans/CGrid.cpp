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
//    CGrid class.
//
//////////////////////////////////////////////////////////////////////
//    Date    Name    Ver     Modification
//    3/4/05    afj     1.0     created
//
//////////////////////////////////////////////////////////////////////

//#pragma warning(disable:4786)
#define DEBUG_FLAG 0
#define DEBUG_TEST 0
#define METHOD_DEBUG 0

//#define PLANE 1

#include "CGrid.h"
#include <iostream>
#include <sstream>
#include <math.h>
//#include "mex.h"

#ifdef LINUX
#include <stdio.h>
#endif    //LINUX

using namespace std;

namespace n_FrameworkLib
{


/****************************************************/
/*        Constructors                                 */
/****************************************************/
CGrid::CGrid(const CGrid& grid) :
//VGrid(0), 
//Index(0),
//UpperBound(0),
//Polygon_Points (0),
xdelta(0),
ydelta(0),
inv_xdelta(0),
inv_ydelta(0),
XGridResolution(0),
YGridResolution(0),
TotalCells(0),
NearEpsilon(1e-9),
dHUGE(1.797693134862315e+308),
GC_BL_IN(0x0001),
GC_BR_IN(0x0002),
GC_TL_IN(0x0004),
GC_TR_IN(0x0008),
GC_L_EDGE_HIT(0x0010),
GC_R_EDGE_HIT(0x0020),
GC_B_EDGE_HIT(0x0040),
GC_T_EDGE_HIT(0x0080),
GC_B_EDGE_PARITY(0x0100),
GC_T_EDGE_PARITY(0x0200),
GC_AIM_L((0<<10)),
GC_AIM_B((1<<10)),
GC_AIM_R((2<<10)),
GC_AIM_T((3<<10)),
GC_AIM_C((4<<10)),
GC_AIM(0x1c00),
GC_L_EDGE_CLEAR(GC_L_EDGE_HIT),
GC_R_EDGE_CLEAR(GC_R_EDGE_HIT),
GC_B_EDGE_CLEAR(GC_B_EDGE_HIT),
GC_T_EDGE_CLEAR(GC_T_EDGE_HIT) 
{  }

// CONSTRUCTOR we want to use!
CGrid::CGrid(std::vector<int32_t>& viVerticies,V_POSITION_t& vposVertexContainer, int x_grid_resolution, 
             int y_grid_resolution, CPosition &min, CPosition &max,
             stringstream &sstrErrorMessage):
//VGrid(0), 
//Index(0),
//UpperBound(0),
//Polygon_Points (polygon_points),
xdelta(0),
ydelta(0),
inv_xdelta(0),
inv_ydelta(0),
XGridResolution(x_grid_resolution),
YGridResolution(y_grid_resolution),
TotalCells(x_grid_resolution*y_grid_resolution),
NearEpsilon(1e-9),
dHUGE(1.797693134862315e+308),
GC_BL_IN(0x0001),
GC_BR_IN(0x0002),
GC_TL_IN(0x0004),
GC_TR_IN(0x0008),
GC_L_EDGE_HIT(0x0010),
GC_R_EDGE_HIT(0x0020),
GC_B_EDGE_HIT(0x0040),
GC_T_EDGE_HIT(0x0080),
GC_B_EDGE_PARITY(0x0100),
GC_T_EDGE_PARITY(0x0200),
GC_AIM_L((0<<10)),
GC_AIM_B((1<<10)),
GC_AIM_R((2<<10)),
GC_AIM_T((3<<10)),
GC_AIM_C((4<<10)),
GC_AIM(0x1c00),
GC_L_EDGE_CLEAR(GC_L_EDGE_HIT),
GC_R_EDGE_CLEAR(GC_R_EDGE_HIT),
GC_B_EDGE_CLEAR(GC_B_EDGE_HIT),
GC_T_EDGE_CLEAR(GC_T_EDGE_HIT)
{
#if DEBUG_FLAG==1
    cout << "CGRid constructor Method\n";
#endif
    
    VGrid.resize(TotalCells);                    // resize array - grab all memory
    glx = new double[XGridResolution+1];                     // do we want vector or array?
    gly = new double[YGridResolution+1];
    int attempt = 0;
    
TryAgain:
    
    xdelta = (max.m_north_m - min.m_north_m)/XGridResolution;
    inv_xdelta = 1.0 / xdelta;
    ydelta = (max.m_east_m - min.m_east_m)/YGridResolution;
    inv_ydelta = 1.0 / ydelta;
    
    
    int i =0;
    for (; i< XGridResolution ; i++) 
        glx[i] = min.m_north_m + i * xdelta;
    glx[i] = max.m_north_m;
    
    for (i =0; i< YGridResolution ; i++) 
        gly[i] = min.m_east_m + i * ydelta;
    gly[i] = max.m_east_m;
    
    UpperBound = VGrid.end();
    
    for ( Index = VGrid.begin(); Index < UpperBound ; Index++) {
        Index->tot_edges = 0;
        Index->gc_flags = 0x0;
        Index->Data = 0;
    }
    
    // loop through edges and insert into grid structure 
//    CPolygon::VPointsIterator vtx0, vtx1;
//    CPolygon::Point *vtxa, *vtxb;
    CPosition *vtxa, *vtxb;
    Cell *p_gc;
    double xdiff, ydiff, tmax, xdir, ydir, t_near, tx, ty, inv_x, inv_y;
    // For distinct locations, there must be a difference in either the north or east directions,
    // so tx and ty can't both be set to dHUGE leading into iterative loop.  The variables tgcx and
    // tgcy used are set in all branches for all other cases, so the conditional branch selected
    // will never try and use the uninitialized tgcx/tgcy.  Both values are initialized to zero
    // to dismiss a compiler warning regarding use of potentially uninitialized variables.
    double tgcx(0), tgcy(0);
    double vx0, vy0, vx1, vy1;
    int gcx, gcy, sign_x, y_flag;
//    vtx0 = (Polygon_Points.end() - 1 );
    
//    for ( vtx1 = Polygon_Points.begin() ; vtx1 < Polygon_Points.end() ; vtx1++ ) {
    for (size_t iVertexIndex1=0,iVertexIndex0=(viVerticies.size()-1);iVertexIndex1<viVerticies.size();iVertexIndex1++ ) 
    {
        
        if (vposVertexContainer[viVerticies[iVertexIndex0]].m_east_m < vposVertexContainer[viVerticies[iVertexIndex1]].m_east_m) 
        {
            vtxa = &vposVertexContainer[viVerticies[iVertexIndex0]] ;
            vtxb = &vposVertexContainer[viVerticies[iVertexIndex1]] ;
        } else {
            vtxa = &vposVertexContainer[viVerticies[iVertexIndex1]] ;
            vtxb = &vposVertexContainer[viVerticies[iVertexIndex0]] ;
        }
        
        // Set x variable for the direction of the ray 
        xdiff = vtxb->m_north_m - vtxa->m_north_m ;
        ydiff = vtxb->m_east_m - vtxa->m_east_m;
        tmax = sqrt( xdiff * xdiff + ydiff * ydiff ) ;
        
        // if edge is of 0 length, ignore it (useless edge) 
        if  ( tmax != 0.0 ) {
            
            xdir = xdiff / tmax ;
            ydir = ydiff / tmax ;
            
            gcx = (int)(( vtxa->m_north_m - min.m_north_m ) * inv_xdelta) ;
            gcy = (int)(( vtxa->m_east_m - min.m_east_m ) * inv_ydelta) ;
            
            // get information about slopes of edge, etc 
            if ( vtxa->m_north_m == vtxb->m_north_m ) {
                sign_x = 0 ;
                tx = dHUGE ;
            } else {
                inv_x = tmax / xdiff ;
                tx = xdelta * (double)gcx + min.m_north_m - vtxa->m_north_m ;
                if ( vtxa->m_north_m < vtxb->m_north_m ) {
                    sign_x = 1 ;
                    tx += xdelta ;
                    tgcx = xdelta * inv_x ;
                } else {
                    sign_x = -1 ;
                    tgcx = -xdelta * inv_x ;
                }
                tx *= inv_x ;
            }
            
            if ( vtxa->m_east_m == vtxb->m_east_m ) {
                ty = dHUGE ;
            } else {
                inv_y = tmax / ydiff ;
                ty = (ydelta * (double)(gcy+1) + min.m_east_m - vtxa->m_east_m)* inv_y ;
                tgcy = ydelta * inv_y ;
            }
#if DEBUG_FLAG==1
            if ( gcy*XGridResolution+gcx > 24 )
                cout << "ERROR!\n";
#endif
            p_gc = &(VGrid.at(gcy*XGridResolution+gcx));
            
            vx0 = vtxa->m_north_m ;
            vy0 = vtxa->m_east_m ;
            
            t_near = 0.0 ;
            do {
                
                if ( tx <= ty ) {
                    gcx += sign_x ;
                    
                    ty -= tx ;
                    t_near += tx ;
                    tx = tgcx ;
                    
                    // note which edge is hit when leaving this cell 
                    if ( t_near < tmax ) {
                        if ( sign_x > 0 ) {
                            p_gc->gc_flags |= GC_R_EDGE_HIT ;
                            vx1 = glx[gcx] ;
                        } else {
                            p_gc->gc_flags |= GC_L_EDGE_HIT ;
                            vx1 = glx[gcx+1] ;
                        }
                        
                        // get new location 
                        vy1 = t_near * ydir + vtxa->m_east_m ;
                    } else {
                        // end of edge, so get exact value 
                        vx1 = vtxb->m_north_m ;
                        vy1 = vtxb->m_east_m ;
                    }
                    
                    y_flag = false ;
                    
                } else {
                    
                    gcy++ ;
                    
                    tx -= ty ;
                    t_near += ty ;
                    ty = tgcy ;
                    
                    // note top edge is hit when leaving this cell 
                    if ( t_near < tmax ) {
                        p_gc->gc_flags |= GC_T_EDGE_HIT ;
                        // this toggles the parity bit 
                        p_gc->gc_flags ^= GC_T_EDGE_PARITY ;
                        
                        // get new location 
                        vx1 = t_near * xdir + vtxa->m_north_m ;
                        vy1 = gly[gcy] ;
                    } else {
                        // end of edge, so get exact value 
                        vx1 = vtxb->m_north_m ;
                        vy1 = vtxb->m_east_m ;
                    }
                    
                    y_flag = true ;
                }
#if DEBUG_FLAG==1
                cout << " b4 setup grid data \n";
#endif
                // check for corner crossing, then mark the cell we're in 
                if (! Setup_GridData(*p_gc, vx0, vy0, vx1, vy1, *vtxa, *vtxb, sstrErrorMessage)) {
                    // warning, danger - we have just crossed a corner.
                    // There are all kinds of topological messiness we could
                    // do to get around this case, but they're a headache.
                    // The simplest recovery is just to change the extents a bit
                    // and redo the meshing, so that hopefully no edges will
                    // perfectly cross a corner.  Since it's a preprocess, we
                    // don't care too much about the time to do it.
                    //
                    
                    //                    cout << "WARNING CORNER PROBLEMS - redo structure!\n";
                    //                    sstrErrorMessage << "WARNING CORNER PROBLEMS - redo structure!\n";
                    // clean out all grid records 
                    
                    if ( VGrid.size()) {                        // skip if size = 0 - nothing to delete
                        
                        UpperBound = VGrid.end();
                        
                        // Delete Cell structures 
                        
                        for (Index = VGrid.begin(); Index < UpperBound ; Index ++ ) {
#if DEBUG_FLAG==1
                            cout << "deleting Grid Cell Data\n";
#endif
                            // delete *Index if not null
                            if (Index->Data) {
                                Index->Data->clear();
                                delete (Index->Data);
                                Index->Data = 0;
                            }
                        }
                        
                    }
                    
                    /* make the bounding box ever so slightly larger, hopefully
                    * changing the alignment of the corners.
                    */
                    xdiff = max.m_north_m - min.m_north_m;
                    ydiff = max.m_east_m - min.m_east_m;
                    double EPSILON = .00001;
                    if (min.m_north_m < ( min.m_north_m - (EPSILON * xdiff * 0.24) ) ) 
                        sstrErrorMessage << "rescale X ERRORR!! EROOR!!! \n";
                    if (min.m_east_m < ( min.m_east_m - (EPSILON * ydiff * 0.10 ) ) )
                        sstrErrorMessage << "rescale Y ERROR!! ERROR!! \n";
                    min.m_north_m -= EPSILON * xdiff * 0.24 ;
                    min.m_east_m -= EPSILON * ydiff * 0.10 ;
                    
                    /* yes, it's the dreaded goto - run in fear for your lives! */
                    attempt++;
#if DEBUG_FLAG==1
                    if (attempt > 5 ) {
                        sstrErrorMessage << "WARNING!!!  loooping at tryagain!\n";
                        //return;
                    }
#endif
                    goto TryAgain ; 
                }
                if ( t_near < tmax ) {
                    // note how we're entering the next cell
                    // TBD: could be done faster by incrementing index in the
                    // incrementing code, above 
#if DEBUG_FLAG==1
                    if((gcy*XGridResolution+gcx) >  24) {
                        sstrErrorMessage << "WARNING!!!\n";
                    }
#endif
                    p_gc = &(VGrid.at(gcy*XGridResolution+gcx) );
                    
                    if ( y_flag ) {
                        p_gc->gc_flags |= GC_B_EDGE_HIT ;
                        // this toggles the parity bit 
                        p_gc->gc_flags ^= GC_B_EDGE_PARITY ;
                    } else {
                        p_gc->gc_flags |=
                            ( sign_x > 0 ) ? GC_L_EDGE_HIT : GC_R_EDGE_HIT ;
                    }
                }
                
                vx0 = vx1 ;
                vy0 = vy1 ;
            }
            
            // have we gone further than the end of the edge? 
            while ( t_near < tmax ) ;
            
        }
        iVertexIndex0 = iVertexIndex1 ;
    } 
    vtxa = 0;    //we don't own this
    vtxb = 0;    //we don't own this

    // grid is all setup, now set up the inside/outside value of each corner.
    Setup_Corner_Value(sstrErrorMessage);
    
}


CGrid::~CGrid() 
{
#if DEBUG_FLAG==1
    if (METHOD_DEBUG)
        cout << "CGrid destructor Method\n";
#endif
    
    stringstream sstrPrintMessage;
    
    if ( VGrid.size() ) {                        // skip if zero lenght - nothing to delete
        
        UpperBound = VGrid.end();
        
        // Delete Cell structures and then clear vector
        
        for (Index = VGrid.begin() ; Index < UpperBound ; Index ++ ) {
#if DEBUG_FLAG==1
            if (DEBUG_FLAG) 
                sstrPrintMessage << "deleting Grid \"CellData\"\n";
#endif
            
            // delete *Index if not null
            if (Index->Data) {
                (*Index->Data).clear();        // clear vector
                delete Index->Data;            // delete vector
            }
            
        }
        VGrid.clear();                    // clear vector
        //    delete (VGrid);                    // delete VGrid
    }
    delete[] glx;
    delete[] gly;
    
#if DEBUG_FLAG==1
    if (DEBUG_FLAG) 
        cout << sstrPrintMessage.str();
    //mexPrintf(sstrPrintMessage.str().c_str())
#endif
}

void CGrid::Setup_Corner_Value(stringstream &sstrErrorMessage)  {
#if DEBUG_FLAG==1
    if (METHOD_DEBUG)
        cout << "Cgrid Setup_Corner_Value() Method\n";
    
    
    sstrErrorMessage << "Inside method setup_corner_value \n";
#endif
    
    // Grid all set up, now set up the inside/outside value of each corner.
    Index = VGrid.begin();
    VCellIterator Index_Next = (VGrid.begin() + XGridResolution);
    UpperBound = VGrid.end();
    
    int io_state;
    
    // we know the bottom and top rows are all outside, so no flag is set 
    for (int i = 1; i < YGridResolution ; i++) {
        
        // start outside 
        io_state = 0x0;   // reset each y turn 
        
        for (int j = 0 ; j < XGridResolution ; j++ ) {
            
            if (io_state) {
                // change cell left corners to inside
                Index->gc_flags |= GC_TL_IN;
                Index_Next->gc_flags |= GC_BL_IN;
            }
            
            if (Index->gc_flags & GC_T_EDGE_PARITY ) 
                io_state = !io_state;
            
            if (io_state) {
                // change cell right corners to inside 
                Index->gc_flags |= GC_TR_IN;
                Index_Next->gc_flags |= GC_BR_IN;
            }
            
            Index++; 
            Index_Next++; 
        }
    } 
    for (Index = VGrid.begin() ; Index < UpperBound ; Index++) {
        // reverse parity of edge clear - ( now 1 means edge clear ) 
        unsigned short gc_clear_flags = Index->gc_flags ^ GC_ALL_EDGE_CLEAR;
        
        if (gc_clear_flags & GC_L_EDGE_CLEAR) {
            Index->gc_flags |= GC_AIM_L;
        } else if (gc_clear_flags & GC_B_EDGE_CLEAR) {
            Index->gc_flags |= GC_AIM_B;
        } else if ( gc_clear_flags & GC_R_EDGE_CLEAR) {
            Index->gc_flags |= GC_AIM_R;
        } else if ( gc_clear_flags & GC_T_EDGE_CLEAR) {
            Index->gc_flags |= GC_AIM_T;
        } else {
            // all edges are intersected on them, do full test 
            Index->gc_flags |= GC_AIM_C;
        }
    } 
#if DEBUG_FLAG==1
    Print();
#endif
}

void CGrid::Print() {
    if (METHOD_DEBUG)
        cout << "Cgrid Print() Method\n";
    
    UpperBound = VGrid.end();
    int i = 0;
    
    for (Index = VGrid.begin() ; Index < UpperBound ; Index++) {
        cout << "\n Grid Cell " << i++ << "\n";
        printf("\nTOTAL EDGES:    %d    GC_FLAGS:    %u\n", Index->tot_edges, Index->gc_flags );
        
        if (Index->Data) {
            DUpperBound = Index->Data->end();
            
            for (DIndex = Index->Data->begin(); DIndex < DUpperBound ; DIndex++) {
                
                cout << "    xa,ya: " << DIndex->xa << "," << DIndex->ya << " ax, ay: " << DIndex->ax << "," << DIndex->ay << " slope " << DIndex->slope << "\n";
                cout << "    minx: " << DIndex->minx << " maxx: " << DIndex->maxx << " miny: " << DIndex->miny << " maxy: " << DIndex->maxy << "\n";
                cout << "    Vertex: (" << DIndex->VertexA.m_north_m <<" , " << DIndex->VertexA.m_east_m <<") , ( " << DIndex->VertexB.m_north_m << ", " << DIndex->VertexB.m_east_m << " ) \n";
            }
        }     
    }
}

bool CGrid::Setup_GridData(Cell &Cur_Cell, double xa, double ya, double xb, double yb, CPosition &vtxa, CPosition &vtxb, stringstream &sstrErrorMessage) {
#if DEBUG_FLAG==1
    cout << "Cgrid Setup_GRidData() Method\n";
    sstrErrorMessage << "Inside Method Setup_GridData\n";
#endif
    
    double slope, inv_slope;
    
    if ( Near(ya, yb, NearEpsilon) ) {
        if ( Near(xa, xb, NearEpsilon) ) {
            /* edge is 0 length, so get rid of it */
            return false;
        } else {
            /* horizontal line */
            slope = dHUGE ;
            inv_slope = 0.0 ;
        }
    } else {
        if ( Near(xa, xb, NearEpsilon) ) {
            /* vertical line */
            slope = 0.0 ;
            inv_slope = dHUGE ;
        } else {
            slope = (xb-xa)/(yb-ya) ;
            inv_slope = (yb-ya)/(xb-xa) ;
        }
    }
    
    Cur_Cell.tot_edges++;
    if ( Cur_Cell.tot_edges <= 1) 
        Cur_Cell.Data = new VData(1);
    else
        Cur_Cell.Data->resize(Cur_Cell.tot_edges);
    
    DUpperBound = ( Cur_Cell.Data->end() - 1 );
    
    DUpperBound->slope = slope ;
    DUpperBound->inv_slope = inv_slope ;
    
    DUpperBound->xa = xa ;
    DUpperBound->ya = ya ;
    
    if ( xa <= xb ) {
        DUpperBound->minx = xa ;
        DUpperBound->maxx = xb ;
    } else {
        DUpperBound->minx = xb ;
        DUpperBound->maxx = xa ;
    }
    if ( ya <= yb ) {
        DUpperBound->miny = ya ;
        DUpperBound->maxy = yb ;
    } else {
        DUpperBound->miny = yb ;
        DUpperBound->maxy = ya ;
    }
    
    /* P2 - P1 */
    DUpperBound->ax = xb - xa ;
    DUpperBound->ay = yb - ya ;
    
    DUpperBound->VertexA = vtxa;
    DUpperBound->VertexB = vtxb;
    
    return true;
}


bool CGrid::InPolygon(double x, double y, double z, const CPosition &min, stringstream &sstrErrorMessage) {
    
#if DEBUG_FLAG==1
    cout << "Cgrid InPolygon() Method\n";
#endif
    
    bool inside_flag = false;
    Cell *p_gc = NULL;
    double bx = 0, by = 0, cx = 0, cy= 0, alpha=0, beta=0, cornerx=0, cornery=0, denom=0;    
    
    // What cell are we in?
    double ycell = ( y - min.m_east_m ) * inv_ydelta;
    double xcell = ( x - min.m_north_m ) * inv_xdelta;
    if (((int) ycell) * XGridResolution + (int)xcell > 24 ) {
        cout << "ERROR!!! \n";
    }
    p_gc = &(VGrid.at( ((int) ycell) * XGridResolution + (int)xcell ));
    
    int count = p_gc->tot_edges;
    
    // is cell simple?
    if (! count) {
        
        // simple cell, so if left lower corner is in, then cell is inside.
        inside_flag =  ( p_gc->gc_flags & GC_BL_IN ) ? 1 : 0 ;
#if DEBUG_FLAG==1
        cout << " Found Simple Cell \n";
#endif
    } else {
        
        /* no, so find an edge which is free. */
        unsigned short gc_flags = p_gc->gc_flags ;
        VData *p_gr = p_gc->Data;
        
        DIndex = p_gr->begin();
        DUpperBound = p_gr->end();
        
        switch (gc_flags & GC_AIM ) {
            // CASE 1:   left edge is clear, shoot X- ray 
            //    GC_AIM_L
        case (0<<10):                // aim towards bottom edge
            //left edge is clear, shoot X-ray
            inside_flag = (gc_flags & GC_BL_IN)? 1 : 0 ;
            
            for ( ; DIndex < DUpperBound ; DIndex++ ) {
                
                // test if y is between edges 
                if ( y >= DIndex->miny && y < DIndex->maxy ) {
                    
                    if ( x > DIndex->maxx ) {
                        
                        inside_flag = !inside_flag ;
                        
#if DEBUG_FLAG==1
                        cout << " case 1 (a) - x > maxx test \n" ;
#endif
                        
                    } else if ( x > DIndex->minx ) {
                        
                        // full computation 
                        if ( ( DIndex->xa -    ( DIndex->ya - y ) * DIndex->slope ) < x )  {
                            inside_flag = !inside_flag ;
                            
#if DEBUG_FLAG==1
                            cout << " case 1 (b) - full computation \n";
#endif
                        }
                    }
                }
            }
            break;                // end left edge clear case
            
            // CASE 2: bottom edge is clear, shoot Y+ ray 
        case (1<<10):
            
            // note - this next statement requires that GC_BL_IN is 1 
            inside_flag = (gc_flags & GC_BL_IN ) ? 1 : 0 ;
            
            for ( ; DIndex < DUpperBound ; DIndex++ ) {
                
                // test if x is between edges 
                if ( x >= DIndex->minx && x < DIndex->maxx ) {
                    
                    if ( y > DIndex->maxy ) {
                        
                        inside_flag = !inside_flag ;
#if DEBUG_FLAG==1
                        cout << "case 2 (a) - y > maxy test \n";
#endif
                        
                    } else if ( y > DIndex->miny ) {
                        // full computation 
                        
                        if ( ( DIndex->ya - ( DIndex->xa - x ) * DIndex->inv_slope ) < y ) {
                            inside_flag = !inside_flag ;
                            
#if DEBUG_FLAG==1
                            cout << "case 2 (b) - full computation \n";
#endif
                        }
                    }
                }
            }
            break;            // end bottom edge clear case
            
            // CASE 3:    right edge is clear, shoot X+ ray 
        case (2<<10):
            inside_flag = (gc_flags & GC_TR_IN) ? 1 : 0 ;
            // TBD: Note, we could have sorted the edges to be tested
            // by miny or somesuch, and so be able to cut testing
            // short when the list's miny > point.y .
            
            for ( ; DIndex < DUpperBound ; DIndex++ ) {
                
                // test if y is between edges 
                if ( y >= DIndex->miny && y < DIndex->maxy ) {
                    
                    if ( x <= DIndex->minx ) {
                        
                        inside_flag = !inside_flag ;
                        
#if DEBUG_FLAG==1
                        cout << "case 3 (a) - y > maxy test \n";
#endif
                        
                    } else if ( x <= DIndex->maxx ) {
                        
                        // full computation 
                        if ( ( DIndex->xa - ( DIndex->ya - y ) * DIndex->slope ) >= x ) {
                            inside_flag = !inside_flag ;
#if DEBUG_FLAG==1
                            cout << "case 3 (b) - full computation \n";
#endif
                        }
                    }
                }
            }
            break;        // end right edge clear case
            
            // CASE 4:    top edge is clear, shoot Y+ ray 
        case (3<<10):
            inside_flag = (gc_flags & GC_TR_IN) ? 1 : 0 ;
            for ( ; DIndex < DUpperBound ; DIndex++ ) {
                // test if x is between edges 
                if ( x >= DIndex->minx && x < DIndex->maxx ) {
                    if ( y <= DIndex->miny ) {
                        inside_flag = !inside_flag ;
                        
#if DEBUG_FLAG==1
                        cout << "case 4 (a) - y <= miny test \n";
#endif
                    } else if ( y <= DIndex->maxy ) {
                        // full computation 
                        if ( ( DIndex->ya - ( DIndex->xa - x ) * DIndex->inv_slope ) >= y ) {
                            inside_flag = !inside_flag ;
#if DEBUG_FLAG==1
                            cout << "case 4 (b) - full computation \n";
#endif
                        }
                    }
                }
            }
            break;
            
            // CASE 5:    no edge is clear, test against the bottom left corner.
        case (4<<10):
            //    We use Franklin Antonio's algorithm (Graphics Gems III).
            
            //    TBD: Faster yet might be to test against the closest
            //    corner to the cell location, but our hope is that we
            //    rarely need to do this testing at all.
            inside_flag = ((gc_flags & GC_BL_IN) == GC_BL_IN) ;
            
            /// get lower left corner coordinate 
            cornerx = glx[ (int)xcell ];
            cornery = gly[ (int)ycell ];
            
            for ( ; DIndex < DUpperBound ; DIndex++ ) {
                
                // quick out test: if test point is
                // less than minx & miny, edge cannot overlap.
                
                if ( x >= DIndex->minx && y >= DIndex->miny ) {
                    
                    // quick test failed, now check if test point and
                    // corner are on different sides of edge.
                    
                    if ( ! bx ) {
                        // Compute these at most once for test: P3 - P4 
                        bx = x - cornerx ;
                        by = y - cornery ;
                    }
                    
                    denom = DIndex->ay * bx - DIndex->ax * by ;
                    
                    if ( denom != 0.0 ) {
                        
                        // lines are not collinear, so continue: P1 - P3 
                        cx = DIndex->xa - x ;
                        cy = DIndex->ya - y ;
                        alpha = by * cx - bx * cy ;
                        beta = DIndex->ax * cy - DIndex->ay * cx ;
                        
                        if ( ( denom > 0.0 ) && 
                            (  ! ( alpha < 0.0 || alpha >= denom )             // test edge hit 
                            &&  ! ( beta < 0.0 || beta >= denom ) ) ) {        // polygon edge hit 
                            
                            inside_flag = !inside_flag;
#if DEBUG_FLAG==1
                            cout << " case 5 (a) \n";
#endif
                        }
                        if ( ( denom < 0.0 ) &&
                            (  ! ( alpha > 0.0 || alpha <= denom )            // test edge hit 
                            && ! ( beta > 0.0 || beta <= denom ) ) ) {        // polygon edge hit 
                            
                            inside_flag = !inside_flag ;
#if DEBUG_FLAG==1
                            cout << " case 5 (b) \n";
#endif
                        }
                    }
                    
                }
                
            }
            break;
            
        default:
            sstrErrorMessage << "WARNING! should never end up HERE! \n" ;
            sstrErrorMessage << "HERE is in the default of case statement of method InPolygon of class CGrid\n";
            break;
        }
        //        cout << "after main test " << endl;
        // double check not on vertex or line if false
        // better to save points in structure and not test whole thing 
        // but do this later
        if ((!inside_flag) && (count) ){
            DIndex = p_gr->begin();
            
            CPosition *vertexA = 0, *vertexB = 0;
            CPosition posX(x,y);
            
            for ( ; DIndex < DUpperBound ; DIndex++ )
                        {
                                //def is_on(a, b, c):
                                //    "Return true iff point c intersects the line segment from a to b."
                                //    # (or the degenerate case that all 3 points are coincident)
                                //    return (collinear(a, b, c)
                                //            and (within(a.x, c.x, b.x) if a.x != b.x else 
                                //                 within(a.y, c.y, b.y)))
                                //
                                //def collinear(a, b, c):
                                //    "Return true iff a, b, and c all lie on the same line."
                                //    return (b.x - a.x) * (c.y - a.y) == (c.x - a.x) * (b.y - a.y)
                                //
                                //def within(p, q, r):
                                //    "Return true iff q is between p and r (inclusive)."
                                //    return p <= q <= r or r <= q <= p        
                            
                            // OR
                            //
                                //def distance(a,b):
                                //    return sqrt((a.x - b.x)**2 + (a.y - b.y)**2)
                                //
                                //def is_between(a,c,b):
                                //    return distance(a,c) + distance(c,b) == distance(a,b)


                vertexA = &DIndex->VertexA; 
                vertexB = &DIndex->VertexB;
                //    cout << " Points tested are: (" << vertexA->X << ", " << vertexA->Y << ")  & ( " << vertexB->X << ", " << vertexB->Y << ") \n";
                                double dDistanceAtoB = vertexA->relativeDistance2D_m(*vertexB);
                                double dDistanceAtoX = vertexA->relativeDistance2D_m(posX);
                                double dDistanceBtoX = vertexB->relativeDistance2D_m(posX);
                                double dResult = dDistanceAtoX + dDistanceBtoX - dDistanceAtoB;
                if (fabs(dResult) < 1.0e-2 )
                                {
                                    inside_flag = 1;
                                    break;
                }
            } 
        } 
    }
    return inside_flag;
}

};      //namespace n_FrameworkLib
              
