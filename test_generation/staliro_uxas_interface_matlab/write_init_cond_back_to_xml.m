function [ savedFiles ] = write_init_cond_back_to_xml( msgToSendFolder, newFilePrefix, initCond, initCondFieldMapping )
%write_init_cond_back_to_xml Saves the used initial conditions into xml
%files.
xmlStruct = [];
savedFiles = cell(0);
index = 0;

xmlFileArr = dir([msgToSendFolder,'/**/*.xml']);
for fileInd = 1:length(xmlFileArr)
    curXmlFile = xmlFileArr(fileInd);
    
    found = 0;
    for initFileInd = 1:length(initCondFieldMapping)
        initCondFileName = initCondFieldMapping{initFileInd}{2};
        if strcmpi(curXmlFile.name, initCondFileName)
            found = found +1;
            if found == 1
                fileFullName = [curXmlFile.folder, '/', curXmlFile.name];
                xmlStruct = xml2struct(fileFullName);
                newFileName = [newFilePrefix, '_', curXmlFile.name];
                newFileFullName = ['./test_xml_files/', newFileName];
                % Enable this if you want to save tot he messages to send
                % folder:
                %newFileFullName = [curXmlFile.folder, '/', newFileName];
                if strcmp(newFileName, curXmlFile.name)
                    if ~exist([fileFullName,'.org'], 'file')
                        copyfile(fileFullName, [fileFullName, '.org']);
                    end
                end
            end
            eval(['xmlStruct.', initCondFieldMapping{initFileInd}{3} ,'.Text = ''',num2str(initCond(initCondFieldMapping{initFileInd}{1})), ''';']);
        end
    end
    if found > 0
        struct2xml(xmlStruct, newFileFullName);
        savedFiles{end+1} = newFileFullName;
    end
end
end
