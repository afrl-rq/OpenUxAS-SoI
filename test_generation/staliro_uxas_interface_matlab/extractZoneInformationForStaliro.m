function [ xmlStruct, fileName, polyVertices ] = extractZoneInformationForStaliro( msgToSendFolder, zoneFileName, zoneType )
%extractZoneInformationForStaliro This function goes into the messages
%to send folder and searches for the given zone file. Then it extracts the
%vertices of the zone.
%   Warning! only supports Polygon type zones for now.
%
%   Input parameters:
%   - msgToSendFolder: Path of the top level messages to send folder
%   - zoneFileName: Name of the zone file
%   - zoneType: Zone type as string. ('KeepOutZone'/'KeepInZone')
%
%   Returns: 
%   - xmlStruct: The read xml file converted into a struct.
%   - fileName: Full path to the file.
%   - polyVertices: 2D array of polygon vertices.

fileName = [];
xmlStruct = [];
polyVertices = [];

xmlFileArr = dir([msgToSendFolder,'/**/*.xml']);
for fileInd = 1:length(xmlFileArr)
    curXmlFile = xmlFileArr(fileInd);
    
    if strcmpi(curXmlFile.name, zoneFileName)
        fName = [curXmlFile.folder, '/', curXmlFile.name];
        if ~exist([fName,'.org'], 'file')
            copyfile(fName, [fName, '.org']);
        end
        xmlStruct = xml2struct(fName);
        if strcmpi(zoneType, 'KeepOutZone')
            num_corners = length(xmlStruct.KeepOutZone.Boundary.Polygon.BoundaryPoints.Location3D);
            poly_V = zeros(num_corners, 2);
            for bound_ind = 1:num_corners
                poly_V(bound_ind, 1) = str2double(xmlStruct.KeepOutZone.Boundary.Polygon.BoundaryPoints.Location3D{bound_ind}.Longitude.Text);
                poly_V(bound_ind, 2) = str2double(xmlStruct.KeepOutZone.Boundary.Polygon.BoundaryPoints.Location3D{bound_ind}.Latitude.Text);
            end
            polyVertices = poly_V;           
            fileName = fName;
        elseif strcmpi(zoneType, 'KeepInZone')
            num_corners = length(xmlStruct.KeepInZone.Boundary.Polygon.BoundaryPoints.Location3D);
            poly_V = zeros(num_corners, 2);
            for bound_ind = 1:num_corners
                poly_V(bound_ind, 1) = str2double(xmlStruct.KeepInZone.Boundary.Polygon.BoundaryPoints.Location3D{bound_ind}.Longitude.Text);
                poly_V(bound_ind, 2) = str2double(xmlStruct.KeepInZone.Boundary.Polygon.BoundaryPoints.Location3D{bound_ind}.Latitude.Text);
            end
            polyVertices = poly_V;           
            fileName = fName;
        end
    end
end

end

