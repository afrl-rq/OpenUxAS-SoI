function [ task_ids ] = extractTaskInformationForStaliro( msgToSendFolder )
%extractTaskInformationForStaliro This function goes into the messages
%to send folder and searches for Task ID. This information
%is used to know how many task report will come with the system trajectory.

task_ids = [];

xmlFileArr = dir([msgToSendFolder,'/**/*.xml']);
for fileInd = 1:length(xmlFileArr)
    curXmlFile = xmlFileArr(fileInd);
    fName = [curXmlFile.folder, '/', curXmlFile.name];
    xmlStruct = xml2struct(fName);

    fields = fieldnames(xmlStruct);
    for i = 1:numel(fields)
        if isfield(xmlStruct.(fields{i}), 'TaskID')
            found = false;
            for j = 1:length(task_ids)
                if task_ids(j) == str2double(xmlStruct.(fields{i}).TaskID.Text)
                    found = true;
                    break;
                end
            end
            if ~found
                task_ids(end+1) = str2double(xmlStruct.(fields{i}).TaskID.Text);
            end
        end
    end
end

end
