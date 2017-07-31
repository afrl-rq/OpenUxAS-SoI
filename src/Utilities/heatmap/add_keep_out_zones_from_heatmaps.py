"""
addKeepOutZonesFromHeatmaps.py
Description: A function to generate keepout zone files from heatmap data
Inputs:
    - heatmap_files - array of file paths
        Example: heatmap_files =
        ['(pathTo)/OpenUxAS/src/Utilities/heatmap/stealthHeatmapData.csv',
        (pathTo)/OpenUxAS/src/Utilities/heatmap/failprobHeatmapData.csv]
    - loc_per_file - level of confidence as cutoff for generating keepOut zones
        The length of locArr needs to be the same as heatmapFileArr.
        Example: loc_per_file = [0.9, 0.95] - This would indicate that keepOut
        zones will be generated for any area of the heatmap over 0.9 and
        0.95.
    - map_center_lat_long_deg - tuple of the latitude and longitude in degrees for the center of the heatmap
    - m_width_m - how wide the map is in meters from the center to the right side
    - m_height_m - how high the map is in meters from the center to the top side
Output:
    - This function will generate keepout zones as KeepOutZone_AutoGen_xxx.xml files.
    - The function is intended to be called from UxAS once a heatmap property is defined
"""
from locale import format

import matplotlib.pyplot as plt
import numpy as np
import LocalCoords
from xml.etree import ElementTree as Et
from shapely.geometry import Polygon
from numpy import genfromtxt
from helper_functions import *
import argparse
import os


def add_keep_out_zones_from_heatmaps(ar_config_file, heatmap_files, loc_per_file, map_center_lat_long_deg, m_width_m,
                                     m_height_m):
    print(' ')
    print('---------------------')
    print('KeepOutZone Generator')
    print('---------------------')
    print(' ')
    # Change debug to 1 to see figures and debugging messages
    debug = 1
    mts_dir = os.path.dirname(ar_config_file)
    # print(mts_dir)
    index = 1

    for idx, file in enumerate(heatmap_files):
        print('Extracting keep out zones from heatmap file #' + str(idx+1) + ' ...')
        # Main function add_heatmaps
        file_appended = 0
        plt.figure(idx)
        if debug == 1: print('File: '+file)
        data = genfromtxt(file, delimiter=',')
        plt.imshow(data, cmap='afmhot', interpolation='nearest')

        lvl_of_conf = float(loc_per_file[idx])
        # print(lvl_of_conf)
        contour_segments = plt.contour(data, levels=[lvl_of_conf], colors=('k',), linestyles=('-',), linewidths=(2,))
        # plt.show()

        # the initial latitude and longitude (linearization point) is set during the first call to LocalCoords:
        LocalCoords.Initialize_deg(float(map_center_lat_long_deg[0]), float(map_center_lat_long_deg[1]))
        linear_coordinates_init = LocalCoords.LatLong_degToNorthEast_m(float(map_center_lat_long_deg[0]), float(map_center_lat_long_deg[1]))
        # print(map_center_lat_long_deg)
        # get right side lat-long-deg
        # linear_coordinates_init
        m_height_m = float(m_height_m)
        m_width_m = float(m_width_m)
        right_coordinate_m = linear_coordinates_init[1]
        top_coordinate_m = linear_coordinates_init[0]

        horiz_m = np.arange(-m_width_m, m_width_m + 2 * m_width_m / (len(data)), 2 * m_width_m/(len(data)-1))
        vert_m = np.arange(-m_height_m, m_height_m + 2 * m_height_m / (len(data)), 2 * m_height_m / (len(data)-1))
        # print(len(vert_m))
        # print(vert_m)
        horiz_m = horiz_m + right_coordinate_m
        vert_m = vert_m + top_coordinate_m
        # print(right_coordinate_m)
        # print(vert_m)

        print("Done")
        print("---------------------")
        # plt.clabel(contour_segments, fmt = '%2.1d', colors = 'k', fontsize=14)
        poly = []
        simp_poly = []
        for collection in contour_segments.collections:
            for path in collection.get_paths():
                poly.append(path.to_polygons())

        for i in range(0, len(poly)):
            # print(poly[i])
            new = np.array(poly[i][0])
            xcol = new[:, 0]
            ycol = new[:, 1]
            xy_data = np.vstack([xcol, ycol]).T
            polygon = Polygon(xy_data)
            simp_poly.append(polygon.simplify(0.99, preserve_topology=True))

        for i in range(0, len(simp_poly)):
            x, y = simp_poly[i].exterior.xy
            # for ii in range(0,len(x)):
            #   plt.scatter(x[ii],y[ii])
            plt.scatter(x, y)



        print("Generating keepout zone files...")
        for ii in range(0, len(poly)):
            x, y = simp_poly[ii].exterior.xy
            root = Et.Element("KeepOutZone", attrib={"Series": "CMASI"})
            Et.SubElement(root, "ZoneType").text = "Physical"
            Et.SubElement(root, "ZoneID").text = str(index)
            Et.SubElement(root, "MinAltitude").text = "-3.40282346638529e+38"
            Et.SubElement(root, "MaxAltitude").text = "3.40282346638529e+38"
            Et.SubElement(root, "AffectedAircraft").text = None
            Et.SubElement(root, "StartTime").text = "0"
            Et.SubElement(root, "EndTime").text = "0"
            Et.SubElement(root, "Padding").text = "60.9599990844727"
            Et.SubElement(root, "Label").text = "KeepOut_AutoGen_" + str(index)

            # Setting bounds
            bnd = Et.SubElement(root, "Boundary")
            poly_xml = Et.SubElement(bnd, "Polygon", attrib={"Series": "CMASI"})
            bnd_pts = Et.SubElement(poly_xml, "BoundaryPoints")

            loc = [Et.Element("") for jj in range(0, len(x))]
            # print(vert_m(x[1])
            # print(horiz_m(x[1])
            for kk in range(0, len(x)):
                loc[kk] = Et.SubElement(bnd_pts, "Location3D",  attrib={"Series": "CMASI"})
                coordinates_lat_long = LocalCoords.NorthEast_mToLatLong_deg(vert_m[round(y[kk])], horiz_m[round(x[kk])])
                # print("coord:")
                # print(coordinates_lat_long)
                Et.SubElement(loc[kk], "Latitude").text = str(coordinates_lat_long[0])
                Et.SubElement(loc[kk], "Longitude").text = str(coordinates_lat_long[1])

            indent(root)
            tree = Et.ElementTree(root)
            f_path = mts_dir + "/MessagesToSend/KeepOutZone_AutoGen_" + str(index) + ".xml"
            print(f_path)
            tree.write(f_path, encoding='utf-8', method="xml")
            print("FILE GENERATED: " + "MessagesToSend/KeepOutZone_AutoGen_" + str(index) + ".xml")
            index += 1

        if debug == 1:
            plt.gca().invert_yaxis()
            plt.show()


    print('')
    print("Generating operating region file...")
    # Add Operating Region File
    or_root = Et.Element("OperatingRegion", attrib={"Series": "CMASI"})
    Et.SubElement(or_root, "ID").text = "314"
    or_ko = Et.SubElement(or_root, "KeepOutAreas")
    for ii in range(1, index):
        Et.SubElement(or_ko, "uint32").text = str(ii)
    indent(or_root)
    or_tree = Et.ElementTree(or_root)
    or_tree.write(mts_dir + "/MessagesToSend/OperatingRegion_Autogen.xml", encoding='utf-8', method="xml")
    print("FILE GENERATED: " + "OperatingRegion_Autogen.xml")

    # Append the automation request configuration file
    ar_doc = Et.parse(ar_config_file)
    root_ar_doc = ar_doc.getroot()

    print('Done... \n')

    print('Appending the automation request file...')

    for service in root_ar_doc.iter('Service'):
        # print(service.attrib)
        if service.attrib['Type'] == 'SendMessagesService':
            send_ms = service

    found_el = 0

    for ii in range(1, index):
        # check if it exists. if not append
        for service in root_ar_doc.iter('Service'):
            for message in service.iter('Message'):
                if message.attrib['MessageFileName'] == 'KeepOutZone_AutoGen_' + str(ii) + '.xml':
                    print('EXISTS: Element ' + 'KeepOutZone_AutoGen_' + str(ii) + '.xml')
                    found_el = 1
                    break

        if found_el == 0:
            add_elem = Et.Element("Message", attrib={"MessageFileName": 'KeepOutZone_AutoGen_' + str(ii) + '.xml',
                                                     "sendTime_ms": "50"})
            send_ms.append(add_elem)
            file_appended = 1
            print('ADDED: ' + 'MessageFileName: KeepOutZone_AutoGen_' + str(ii) + '.xml')
        found_el = 0

    if does_elem_exist(root_ar_doc, 'Service', 'Message', 'MessageFileName', 'OperatingRegion_Autogen.xml') == 0:
        send_ms.append((Et.Element(
            'Message MessageFileName="OperatingRegion_Autogen.xml" SendTime_ms="50"')))
        file_appended = 1

    if file_appended:
        send_ms.append(Et.Comment(
            'AutoGenerated with add_keep_out_zones_from_heatmaps.py'))

    # Check if ar file subscribes to keepoutzone. If not append
    found = 0
    first_bridge = []
    for bridge in root_ar_doc.iter('Bridge'):
        # print(service.attrib)
        for subscribe_to_message in bridge.iter('SubscribeToMessage'):
            if subscribe_to_message.attrib['MessageType'] == 'afrl.cmasi.KeepOutZone':
                found = 1
                print('EXISTS: SubscribeToMessage afrl.cmasi.KeepOutZone')
                break
        first_bridge = bridge

    if found != 1:
        first_bridge.append(Et.Element('SubscribeToMessage MessageType="afrl.cmasi.KeepOutZone"'))
        print('ADDED: MessageType="afrl.cmasi.KeepOutZone')

    print('Done!')

    indent(root_ar_doc)
    ar_doc.write(ar_config_file, encoding='utf-8', method="xml")

parser = argparse.ArgumentParser()
parser.add_argument("-cfg_path")
parser.add_argument("-heatmap_data_list",  nargs='+')
parser.add_argument("-cl_level",  nargs='+')
parser.add_argument("-map_center",  nargs='+')
parser.add_argument("-map_width")
parser.add_argument("-map_height")

args = parser.parse_args()

add_keep_out_zones_from_heatmaps(args.cfg_path, args.heatmap_data_list, args.cl_level, args.map_center, args.map_width, args.map_height)

# add_keep_out_zones_from_heatmaps('/Users/bardhh/uxas_framework/OpenUxAS/examples/02_Example_WaterwaySearch/cfg_WaterwaySearch.xml', ['/Users/bardhh/uxas_framework/OpenUxAS/examples/02_Example_WaterwaySearch/heatmapData/dangerHeatmapData.csv'], ['0.95'], ['45.30','-121'], '11765', '9289')

# add_keep_out_zones_from_heatmaps('/Users/bardhh/uxas_framework/OpenUxAS/examples/02_Example_WaterwaySearch/cfg_WaterwaySearch.xml', ['/Users/bardhh/uxas_framework/OpenUxAS/examples/02_Example_WaterwaySearch/heatmapData/dangerHeatmapData.csv','/Users/bardhh/uxas_framework/OpenUxAS/examples/02_Example_WaterwaySearch/heatmapData/failprobHeatmapData.csv'], ['0.95', '0.95'], ['45.30', '-121'], '11765', '9289')