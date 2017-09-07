function [ initCondFieldMapping, xmlStruct ] = extractInitCondInformationForStaliro( msgToSendFolder )
%extractInitCondInformationForStaliro This function goes into the messages
%to send folder and searches for the fields configured for S-TaLiRo.
%
%   Input parameters:
%   - msgToSendFolder: Path of the top level messages to send folder
%
%   Returns: 
%   - initCondFieldMapping: A data structure containing a mapping from the 
%                           configured fields to the initial conditions.
%   - xmlStruct: The xml file converted into a struct.
%
%   Mapping from fields to init. conditions (more on initCondFieldMapping):
%   A cell array where each entry contains:
%   - index: Index of the parameter in the initial conditions array
%   - recordFName: Name of the file which keeps the parameters
%   - fieldNameDict: A cell array containing the names of the parameters 
%                    (from the same file/structure)
%   - fieldLimitsDict: A cell array containing the lower and upper limits 
%                      for the parameter values.
%   - fieldTypeDict: A cell array containing the type of the parameter 
%                    ("field"/"path"/"zone") Path and zone requires special
%                    treatment.

initCondFieldMapping = cell(0);
xmlStruct = [];
index = 0;

xmlFileArr = dir([msgToSendFolder,'/**/*.xml']);
for fileInd = 1:length(xmlFileArr)
    curXmlFile = xmlFileArr(fileInd);
    fName = [curXmlFile.folder, '/', curXmlFile.name];
    xmlStruct = xml2struct(fName);
    [fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict] = ...
        searchStaliroFields( xmlStruct );
    fileNameStr = erase([curXmlFile.folder, '/', curXmlFile.name], msgToSendFolder);
    for i = 1:length(fieldNameDict)
        index = index + 1;
        if isempty(orgFileNameDict{i})
            recordFName = fileNameStr;
        else
            recordFName = orgFileNameDict{i};
        end
        initCondFieldMapping{end+1} = ...
            {index, recordFName, fieldNameDict{i}, fieldLimitsDict{i}, fieldTypeDict{i}, scenarioFileNameDict{i}, scenarioFieldNameDict{i}};
    end
end

end

