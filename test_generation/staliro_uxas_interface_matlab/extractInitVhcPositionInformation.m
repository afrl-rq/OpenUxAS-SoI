function [ vhcPositionInformation ] = extractInitVhcPositionInformation( msgToSendFolder )
%extractInitVhcPositionInformation This function goes into the messages
%to send folder and searches for the initial vehicle positions.
%
%   Input parameters:
%   - msgToSendFolder: Path of the top level messages to send folder
%
%   Returns: 
%   - vhcPositionInformation: A data structure containing vehicle positions
%                             with ID, position and related file name.

vhcPositionInformation = cell(0);

xmlFileArr = dir([msgToSendFolder,'/**/*.xml']);
for fileInd = 1:length(xmlFileArr)
    curXmlFile = xmlFileArr(fileInd);
    fName = [curXmlFile.folder, '/', curXmlFile.name];
    xmlStruct = xml2struct(fName);
    if isfield(xmlStruct, 'AirVehicleState')
        if isfield(xmlStruct.AirVehicleState, 'Location') && isfield(xmlStruct.AirVehicleState, 'ID')
            if isfield(xmlStruct.AirVehicleState.Location, 'Location3D')
                if isfield(xmlStruct.AirVehicleState.Location.Location3D, 'Latitude') && ...
                        isfield(xmlStruct.AirVehicleState.Location.Location3D, 'Longitude') && ...
                        isfield(xmlStruct.AirVehicleState.Location.Location3D, 'Altitude')
                    vhcPositionInformation{end+1} = ...
                        {str2double(xmlStruct.AirVehicleState.ID.Text), ...
                        str2double(xmlStruct.AirVehicleState.Location.Location3D.Latitude.Text), ...
                        str2double(xmlStruct.AirVehicleState.Location.Location3D.Longitude.Text), ...
                        str2double(xmlStruct.AirVehicleState.Location.Location3D.Altitude.Text), ...
                        curXmlFile.name};
                end
            end
        end
    end
end

end

