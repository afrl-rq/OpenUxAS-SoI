function [ initCondFieldMapping ] = extractOutputInformationForStaliro( msgToReadFolder )
%UNTITLED2 Summary of this function goes here
%   Detailed explanation goes here
initCondFieldMapping = cell(0);
index = 0;

xmlFileArr = dir([msgToReadFolder,'/**/*.xml']);
for fileInd = 1:length(xmlFileArr)
    curXmlFile = xmlFileArr(fileInd);
    fName = [curXmlFile.folder, '/', curXmlFile.name];
    xmlStruct = xml2struct(fName);
    [fieldNameDict, fieldLimitsDict, orgFileNameDict] = searchStaliroFields( xmlStruct );
    fileNameStr = erase([curXmlFile.folder, '/', curXmlFile.name], msgToReadFolder);
    for i = 1:length(fieldNameDict)
        index = index + 1;
        if isempty(orgFileNameDict{i})
            recordFName = fileNameStr;
        else
            recordFName = orgFileNameDict{i};
        end
        initCondFieldMapping{end+1} = {index, recordFName, fieldNameDict{i}, fieldLimitsDict{i}};
    end
end

end

