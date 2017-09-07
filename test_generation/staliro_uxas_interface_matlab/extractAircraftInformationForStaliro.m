function [ vehicle_ids ] = extractAircraftInformationForStaliro( msgToSendFolder )
%extractAircraftInformationForStaliro This function goes into the messages
%to send folder and searches for Aircraft configuration. This information
%is used to match aircraft with the system trajectory.

vehicle_ids = [];

xmlFileArr = dir([msgToSendFolder,'/**/*.xml']);
for fileInd = 1:length(xmlFileArr)
    curXmlFile = xmlFileArr(fileInd);
    fName = [curXmlFile.folder, '/', curXmlFile.name];
    xmlStruct = xml2struct(fName);
    if exists(xmlStruct, 'AirVehicleConfiguration')
        vehicle_ids(end+1) = str2double(xmlStruct.AirVehicleConfiguration.ID.Text);
    end
end

end
