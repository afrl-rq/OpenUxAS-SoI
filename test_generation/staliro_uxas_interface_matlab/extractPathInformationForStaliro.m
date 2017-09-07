function [ xmlStruct, savedFiles, path_pts ] = extractPathInformationForStaliro( msgToSendFolder, pathFileName, pathType )
%extractPathInformationForStaliro This function goes into the messages
%to send folder and searches for the given task file. Then it samples a
%random path from the beginning to the end of the task. Updates the found
%file with the newly sampled path. Saves original file with .org extension.
%Warning! Only works for LineSearchTask for now.
%
%   Input parameters:
%   - msgToSendFolder: Path of the top level messages to send folder
%   - pathFileName: Name of the task file
%   - pathType: Task type as string. ('LineSearchTask')
%
%   Returns: 
%   - xmlStruct: The newly generated xml file converted into a struct.
%   - savedFiles: List of the newly generated files.
%   - path_pts: Points on the newly sampled path for the task.


savedFiles = cell(0);
xmlStruct = [];
path_pts = [];
index = 0;

xmlFileArr = dir([msgToSendFolder,'/**/*.xml']);
for fileInd = 1:length(xmlFileArr)
    curXmlFile = xmlFileArr(fileInd);
    
    if strcmpi(curXmlFile.name, pathFileName)
        fName = [curXmlFile.folder, '/', curXmlFile.name];
        if ~exist([fName,'.org'], 'file')
            copyfile(fName, [fName, '.org']);
        end
        xmlStruct = xml2struct(fName);
        if strcmpi(pathType, 'LineSearchTask')
            start_altitude = str2double(xmlStruct.LineSearchTask.PointList.Location3D{1}.Altitude.Text);
            start_latitude = str2double(xmlStruct.LineSearchTask.PointList.Location3D{1}.Latitude.Text);
            start_longitude = str2double(xmlStruct.LineSearchTask.PointList.Location3D{1}.Longitude.Text);
            end_altitude = str2double(xmlStruct.LineSearchTask.PointList.Location3D{end}.Altitude.Text);
            end_latitude = str2double(xmlStruct.LineSearchTask.PointList.Location3D{end}.Latitude.Text);
            end_longitude = str2double(xmlStruct.LineSearchTask.PointList.Location3D{end}.Longitude.Text);
            xmlStruct.LineSearchTask.PointList.Location3D(2:end) = [];
            path_pts = sample_path([start_latitude, start_longitude, start_altitude], [end_latitude, end_longitude, end_altitude]);
            num_pts = size(path_pts, 1);
            for i = 2:num_pts
                xmlStruct.LineSearchTask.PointList.Location3D{end+1} = xmlStruct.LineSearchTask.PointList.Location3D{end};
                xmlStruct.LineSearchTask.PointList.Location3D{end}.Latitude.Text = num2str(path_pts(i, 1), 16);
                xmlStruct.LineSearchTask.PointList.Location3D{end}.Longitude.Text = num2str(path_pts(i, 2), 16);
                xmlStruct.LineSearchTask.PointList.Location3D{end}.Altitude.Text = num2str(path_pts(i, 3), 16);
            end
            struct2xml(xmlStruct, fName);
            savedFiles{end+1} = fName;
        end
    end
end

end

