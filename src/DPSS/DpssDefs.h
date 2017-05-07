// ===============================================================================
// Authors: AFRL/RQQA
// Organization: Air Force Research Laboratory, Aerospace Systems Directorate, Power and Control Division
// 
// Copyright (c) 2017 Government of the United State of America, as represented by
// the Secretary of the Air Force.  No copyright is claimed in the United States under
// Title 17, U.S. Code.  All Other Rights Reserved.
// ===============================================================================

#pragma once

#ifndef _WIN32
#define DPSS_API 

#else//_WIN32
#ifdef DPSS_EXPORTS
#define DPSS_API __declspec(dllexport)
#else
#define DPSS_API __declspec(dllimport)
#endif
#endif//_WIN32
