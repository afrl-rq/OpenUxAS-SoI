#include <Python.h>
#include "../UnitConversions.h"
#include <iostream>

uxas::common::utilities::CUnitConversions* flatEarth = new uxas::common::utilities::CUnitConversions();

static PyObject *
LatLong_degToNorthEast_m(PyObject *self, PyObject *args)
{
  double easting;
  double northing;
  double lat, lon;
  
  PyArg_ParseTuple(args, "dd",&lat,&lon);
  // std::cout << "******* lat[" << lat << "] lon[" << lon << "] *******" << std::endl;
  flatEarth->ConvertLatLong_degToNorthEast_m(lat,lon,northing,easting);
  return Py_BuildValue("dd",northing,easting);
}

static PyObject *
NorthEast_mToLatLong_deg(PyObject *self, PyObject *args)
{
  double easting;
  double northing;
  double lat, lon;
  
  PyArg_ParseTuple(args, "dd",&northing,&easting);
  flatEarth->ConvertNorthEast_mToLatLong_deg(northing,easting,lat,lon);
  return Py_BuildValue("dd", lat,lon);
}

static PyObject *
LinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(PyObject *self, PyObject *args)
{
  double distance_m;
  double latitude1_deg{0.0};
  double longitude1_deg{0.0};
  double latitude2_deg{0.0};
  double longitude2_deg{0.0};

  PyArg_ParseTuple(args, "dddd",&latitude1_deg,&longitude1_deg,&latitude2_deg,&longitude2_deg);
  // std::cout << "******* latitude1_deg[" << latitude1_deg << "] longitude1_deg[" << longitude1_deg << "] latitude2_deg[" << latitude2_deg << "] longitude2_deg[" << longitude2_deg << "] *******" << std::endl;
  distance_m = flatEarth->dGetLinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg(latitude1_deg,longitude1_deg,latitude2_deg,longitude2_deg);
  return Py_BuildValue("d",distance_m);
}

static PyObject *
Initialize_deg(PyObject *self, PyObject *args)
{
  double lat, lon;
  
  PyArg_ParseTuple(args, "dd",&lat,&lon);
  lat *= n_Const::c_Convert::dDegreesToRadians();
  lon *= n_Const::c_Convert::dDegreesToRadians();
  flatEarth->Initialize(lat,lon);
  return Py_BuildValue("d", 0.0);
}

static PyMethodDef LocalCoordsMethods[] = {
    {"LatLong_degToNorthEast_m",  LatLong_degToNorthEast_m, METH_VARARGS,
     "convert from lat long degrees to meters\n@params lat,lon: all double (float)"},
    {"NorthEast_mToLatLong_deg",  NorthEast_mToLatLong_deg, METH_VARARGS,
     "convert from meters to lat long degrees\n@params northing, easting: all double (float)"},
    {"LinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg",  LinearDistance_m_Lat1Long1_deg_To_Lat2Long2_deg, METH_VARARGS,
     "calculate distance, in meters, between two locations specified in lat long degrees\n@params distance: all double (float)"},
    {"Initialize_deg",  Initialize_deg, METH_VARARGS,
     "Sets the linearization point\n@params latitude, longitude degrees: all double (float)"},
    {NULL, NULL, 0, NULL}        /* Sentinel */
};

PyMODINIT_FUNC
initLocalCoords(void)
{
    (void) Py_InitModule("LocalCoords", LocalCoordsMethods);
}
