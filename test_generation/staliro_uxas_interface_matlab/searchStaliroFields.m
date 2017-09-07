function [fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict] = searchStaliroFields( root )
%searchStaliroFields Searches staliro_minimum and staliro_maximum fields
%inside an xml structure. Returns names of the struct fields and 
%corresponding minimum and maximum values in dictionaries.
%
%   Input parameters:
%   - root: Root of the xml structure
%
%   Returns: 
%   - fieldNameDict: A cell array containing the names of the fields found.
%   - fieldLimitsDict: A cell array containing the ranges for the fields.
%   - orgFileNameDict: A cell array containing the file names in which the
%                      fields are found.
%   - fieldTypeDict: A cell array containting string representation of the
%                    field types. ("field"/"path"/zone")

fieldNameDict = cell(0);
fieldLimitsDict = cell(0);
orgFileNameDict = cell(0);
fieldTypeDict = cell(0);
scenarioFileNameDict = cell(0);
scenarioFieldNameDict = cell(0);

orgFileName = '';

fieldNamesCell = fieldnames(root);
if length(fieldNamesCell) == 1 && (strcmpi(fieldNamesCell{1}, 'STALIRO_INIT_COND') || strcmpi(fieldNamesCell{1}, 'STALIRO_PATH'))
    subRoots = fieldnames(root.(fieldNamesCell{1}));
    for r = 1:length(subRoots)
        for i = 1:length(root.(fieldNamesCell{1}).(subRoots{r}))
            if iscell(root.(fieldNamesCell{1}).(subRoots{r}))
                newRoot = root.(fieldNamesCell{1}).(subRoots{r}){i};
            else
                newRoot = root.(fieldNamesCell{1}).(subRoots{r});
            end
            [fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict] = ...
                iterativeFieldSearch(newRoot, subRoots{r}, orgFileName, fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict);
        end
    end
else
    [fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict] = ...
        iterativeFieldSearch(root, '', orgFileName, fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict);
end

end

function [fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict] = ...
    iterativeFieldSearch(root, rootStr, orgFileName, fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict)
    if isempty(orgFileName)
        if isfield(root, 'Attributes')
            if isfield(root.Attributes, 'OriginalFileName')
                orgFileName = root.Attributes.OriginalFileName;
            end
            if isfield(root.Attributes, 'STaliroProperty')
                if strcmpi(root.Attributes.STaliroProperty, 'GeneratePath')
                    fieldNameDict{end+1} = rootStr;
                    fieldLimitsDict{end+1} = [0,0];
                    orgFileNameDict{end+1} = orgFileName;
                    fieldTypeDict{end+1} = 'path';
                    scenarioFileNameDict{end+1} = '';
                    scenarioFieldNameDict{end+1} = '';
                elseif strcmpi(root.Attributes.STaliroProperty, 'GenerateZone')
                    fieldNameDict{end+1} = rootStr;
                    fieldLimitsDict{end+1} = [0,0];
                    orgFileNameDict{end+1} = orgFileName;
                    fieldTypeDict{end+1} = 'zone';
                    scenarioFileNameDict{end+1} = '';
                    scenarioFieldNameDict{end+1} = '';
                end
            end
        end
    end
    fieldNamesCell = fieldnames(root);
    if any(strcmp(fieldNamesCell,'staliro_minimum')) && any(strcmp(fieldNamesCell,'staliro_maximum'))
        fieldNameDict{end+1} = rootStr;
        minVal = str2double(root.staliro_minimum.Text);
        maxVal = str2double(root.staliro_maximum.Text);
        fieldLimitsDict{end+1} = [minVal, maxVal];
        orgFileNameDict{end+1} = orgFileName;
        fieldTypeDict{end+1} = 'field';
        if any(strcmp(fieldNamesCell,'scenario_file')) && any(strcmp(fieldNamesCell,'scenario_field'))
            scenarioFileNameDict{end+1} = root.scenario_file.Text;
            scenarioFieldNameDict{end+1} = root.scenario_field.Text;
        else
            scenarioFileNameDict{end+1} = '';
            scenarioFieldNameDict{end+1} = '';
        end
    elseif any(strcmp(fieldNamesCell,'staliro_path_start_minimum')) && any(strcmp(fieldNamesCell,'staliro_path_start_maximum'))
        fieldNameDict{end+1} = rootStr;
        minVal = str2double(root.staliro_path_start_minimum.Text);
        maxVal = str2double(root.staliro_path_start_maximum.Text);
        fieldLimitsDict{end+1} = [minVal, maxVal];
        orgFileNameDict{end+1} = orgFileName;
        fieldTypeDict{end+1} = 'path_start';
        scenarioFileNameDict{end+1} = '';
        scenarioFieldNameDict{end+1} = '';
    elseif any(strcmp(fieldNamesCell,'staliro_path_end_minimum')) && any(strcmp(fieldNamesCell,'staliro_path_end_maximum'))
        fieldNameDict{end+1} = rootStr;
        minVal = str2double(root.staliro_path_end_minimum.Text);
        maxVal = str2double(root.staliro_path_end_maximum.Text);
        fieldLimitsDict{end+1} = [minVal, maxVal];
        orgFileNameDict{end+1} = orgFileName;
        fieldTypeDict{end+1} = 'path_end';
        scenarioFileNameDict{end+1} = '';
        scenarioFieldNameDict{end+1} = '';
    else
        for i = 1:length(fieldNamesCell)
            f_arr = root.(fieldNamesCell{i});
            if ~isempty(f_arr) && (isstruct(f_arr(1)) || (iscell(f_arr) && isstruct(f_arr{1}))) % Because f_arr can be string for attributes
                if isempty(rootStr)
                    fieldStr = fieldNamesCell{i};
                else
                    fieldStr = [rootStr, '.', fieldNamesCell{i}];
                end
                for f_i = 1:length(f_arr)
                    if length(f_arr) > 1
                        subRootStr = [fieldStr, '{', num2str(int32(f_i)),'}'];
                    else
                        subRootStr = fieldStr;
                    end
                    if iscell(f_arr)
                        nextRoot = f_arr{f_i};
                    else
                        nextRoot = f_arr(f_i);
                    end
                    [fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict] = ...
                        iterativeFieldSearch(nextRoot, subRootStr, orgFileName, fieldNameDict, fieldLimitsDict, orgFileNameDict, fieldTypeDict, scenarioFileNameDict, scenarioFieldNameDict);
                end
            end
        end
    end
end
