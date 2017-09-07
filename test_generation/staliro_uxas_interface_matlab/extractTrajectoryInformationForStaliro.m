function [ trajectoryMapping, xmlStruct ] = extractTrajectoryInformationForStaliro( msgToSendFolder )
%extractTrajectoryInformationForStaliro This function goes into the messages
%to send folder and searches for the trajectory configuration for S-TaLiRo.
%
%   Input parameters:
%   - msgToSendFolder: Path of the top level messages to send folder
%
%   Returns: 
%   - trajectoryMapping: A data structure containing a mapping from the 
%                        fields to record to positions in the trajectory.
%   - xmlStruct: The xml file converted into a struct.


trajectoryMapping = cell(0);
xmlStruct = [];

xmlFileArr = dir([msgToSendFolder,'/**/*.xml']);
for fileInd = 1:length(xmlFileArr)
    curXmlFile = xmlFileArr(fileInd);
    fName = [curXmlFile.folder, '/', curXmlFile.name];
    xmlStruct = xml2struct(fName);
    if isfield(xmlStruct, 'STALIRO_TRAJECTORY')
        trajectoryMapping = xmlStruct.STALIRO_TRAJECTORY.TrajectoryRecord;
        break;
    end
end

end

