function [T, X, Y, L, CLG, GRD] = uxas_blackbox(X0,ET,TS,U)
%uxas_blackbox Runs uxas with given initial conditions. Converts trajectory
%into what was expected for robustness computations.
global trajectories;
global initCondFieldMapping;
global initCondZoneMapping;
global taskPaths;
global vhcInitPositions;
global taskMonitoringResults;
global task_ids;

disp(X0')

%UXAS_RUN_DIR = '/home/etuncali/UxAS_pulls/OpenUxAS/examples/07_Test_WaterwaySearch';
%UXAS_RUN_DIR = '/home/parallels/UxAS_pulls/OpenUxAS/examples/07_Test_WaterwaySearch';
UXAS_RUN_DIR = '/Users/erkan/UxASPulls/OpenUxAS/examples/07_Test_WaterwaySearch';
UXAS_RUN_COMMAND = './runUxAS_WaterwaySearch.sh&';
AMASE_RUN_COMMAND = './runAMASE_WaterwaySearch_headless.sh&';
%AMASE_RUN_COMMAND = './runAMASE_WaterwaySearch.sh&';

UXAS_IP_ADDRESS = '127.0.0.1';
UXAS_PORT = 5554;

MAX_NUM_OF_CONNECTION_RETRIES = 300;
% The indices in the trajectory which contains air vehicle positio values.
% Used to interpolate missing entries in case an AirVehicleState message is
% missed in the communication.
AIR_VEHICLE_POSITION_INDICES = [2,3,4,5,6,7,8,9,10,11,12,13];

num_zone_mapping = length(initCondZoneMapping);
zoneX0 = X0(end-2*num_zone_mapping+1:end);
X0(end-2*num_zone_mapping+1:end) = [];

for i = 1:length(vhcInitPositions)
    fName = vhcInitPositions{i}{5};
    for j = 1:length(initCondFieldMapping)
        initCondFName = initCondFieldMapping{j}{2};
        if strcmp(fName, initCondFName)
            fieldName = initCondFieldMapping{j}{3};
            if strcmpi(fieldName, 'AirVehicleState.Location3D.Latitude')
                index = initCondFieldMapping{j}{1};
                vhcInitPositions{i}{2} = X0(index);
            elseif strcmpi(fieldName, 'AirVehicleState.Location3D.Longitude')
                index = initCondFieldMapping{j}{1};
                vhcInitPositions{i}{3} = X0(index);
            elseif strcmpi(fieldName, 'AirVehicleState.Location3D.Altitude')
                index = initCondFieldMapping{j}{1};
                vhcInitPositions{i}{4} = X0(index);
            end
        end
    end
end

taskMonitoringResults = cell(0);
for i = 1:length(task_ids)
    taskMonitoringResults{end+1} = [task_ids(i), 0, 0];
end

zones = cell(0);
for i = 1:num_zone_mapping
    zones{end+1} = placePolyhedron( initCondZoneMapping(i).polyVertices, zoneX0(2*i-1), zoneX0(2*i), taskPaths, vhcInitPositions );
    xmlStruct = initCondZoneMapping(i).xmlStruct;
    for bound_ind = 1:size(zones{end}, 1)
        xmlStruct.KeepOutZone.Boundary.Polygon.BoundaryPoints.Location3D{bound_ind}.Longitude.Text = num2str(zones{end}(bound_ind, 1), 16);
        xmlStruct.KeepOutZone.Boundary.Polygon.BoundaryPoints.Location3D{bound_ind}.Latitude.Text = num2str(zones{end}(bound_ind, 2), 16);
    end

    struct2xml(xmlStruct, initCondZoneMapping(i).fileName);
end

T = [];
X = [];
Y = [];
L = [];
CLG = [];
GRD = [];

orgDir = pwd;
cd(UXAS_RUN_DIR);

% Because some data like AirVehicleConfiguration is duplicate in
% MessagesToSend folder and in scenario configuration xml, and because
% there is no other way to achieve this in the run time, we have to update
% related fields in the scenario configuration xml file before starting Amase.
scenarioXmlStructs = cell(0);
scenarioXmlFiles = cell(0);
for i = 1:length(initCondFieldMapping)
    value_for_field = X0(i);
    if ~isempty(initCondFieldMapping{i}{6})
        scenarioXmlFile = initCondFieldMapping{i}{6};
        found = false;
        found_ind = 0;
        for j = 1:length(scenarioXmlFiles)
            if scenarioXmlFiles{j} == scenarioXmlFile
                found = true;
                found_ind = j;
                scenarioXmlStruct = scenarioXmlStructs{j};
                break;
            end
        end
        if ~found
            scenarioXmlFiles{end+1} = scenarioXmlFile;
            scenarioXmlStruct = xml2struct(initCondFieldMapping{i}{6});
            scenarioXmlStructs{end+1} = scenarioXmlStruct;
            found_ind = length(scenarioXmlStructs);
        end
        if ~isempty(initCondFieldMapping{i}{7})
            scenarioFieldStr = initCondFieldMapping{i}{7};
            eval(['scenarioXmlStructs{', num2str(found_ind) ,'}.', scenarioFieldStr, '.Text = ''', num2str(value_for_field), ''';']);
        end
    end
end
for i = 1:length(scenarioXmlFiles)
    if ~exist([scenarioXmlFiles{i},'.org'], 'file')
        copyfile(scenarioXmlFiles{i}, [scenarioXmlFiles{i}, '.org']);
    end
    struct2xml(scenarioXmlStructs{i}, scenarioXmlFiles{i});
end

num_tries = 0;
while num_tries < 10
    try
        system(UXAS_RUN_COMMAND);
        pause(1);
        uxasCom = UxASCommunicator(UXAS_IP_ADDRESS, UXAS_PORT);
        connectTryCount = 0;
        while strcmpi(uxasCom.sock.Status, 'closed')
            uxasCom.connect();
            pause(0.1);
            connectTryCount = connectTryCount + 1;
            if connectTryCount > MAX_NUM_OF_CONNECTION_RETRIES
                break;
            end
        end
        if strcmpi(uxasCom.sock.Status, 'open')
            disp('Connected to UxAS.');
            ack = uxasCom.sendInitCond(X0, initCondFieldMapping);
            disp(['Sent init cond. ', num2str(ack)]);
            pause(0.1);
            ack = uxasCom.startSim(ET);
            disp(['Started Simulation...', num2str(ack)]);
            pause(0.1);
            system(AMASE_RUN_COMMAND);
            isEndOfSimulation = 0;
            disp('Simulation Status:          Starting');
            while isEndOfSimulation == 0
                [isEndOfSimulation, curSimTime, totalSimTime] = uxasCom.receiveSimulationStatus();
                if curSimTime >= totalSimTime
                    isEndOfSimulation = 1;
                end
            end
                
            [X, listOfVehiclesAndIndices] = uxasCom.receiveTrajectory();
            isEndOfSimulation = 0;
            while isEndOfSimulation == 0
                [isEndOfSimulation, task_id, task_status, task_robustness] = uxasCom.receiveTaskStatus();
                if task_id > 0
                    for t_i = 1:length(taskMonitoringResults)
                        if taskMonitoringResults{t_i}(1) == task_id
                            taskMonitoringResults{t_i} = [task_id, task_status, task_robustness];
                        end
                    end
                end
                if isEndOfSimulation
                    fprintf('END OF SIMULATION!')
                else
                    fprintf('task: %d, status: %d, robustness: %g\n', task_id, task_status, task_robustness);
                end
            end
            disp('Received ');
        else
            disp('COULD NOT CONNECT to UxAS');
            disp(['Make sure UxAS is running, and the SendTestMessages service is on and configured to connect on ', UXAS_IP_ADDRESS, ':', num2str(UXAS_PORT)])
        end
        num_tries = 10; % To make it exit because this was a success
        try
            uxasCom.disconnect();
        catch
            disp('CAN NOT DISCONNECT!');
        end
    catch
        disp(['... RETRYING TO EXECUTE (' , num2str(num_tries) ,')...']);
        try
            uxasCom.disconnect();
        catch
            disp('CAN NOT DISCONNECT!');
        end
        system('killall uxas');
        amase_pid = getpidof_java('Amase');
        if ~isempty(amase_pid)
            cmd = ['kill ', num2str(amase_pid)];
            system(cmd);
        end
        pause(3);
    end
    num_tries = num_tries + 1;
end
disp('finished!')

cd(orgDir);

system('killall uxas');
amase_pid = getpidof_java('Amase');
if ~isempty(amase_pid)
    cmd = ['kill ', num2str(amase_pid)];
    system(cmd);
end


[ X ] = interpolateAirVehicleState( X, AIR_VEHICLE_POSITION_INDICES );
T = X(:, 1);

% Extract distance to keep out zones information from the positions:
% There are too many hard coded things here.
if size(X, 1) > 0
    size_of_a_record = length(X(1, :));
else
    size_of_a_record = 0;
end

% Computing the distance to keep out zones and adding them to the
% trajectory.
% Randomly placed zones will automatically be in the zones{} cell array.
% However, we should add the other zones which are not randomly placed.
zones{end+1} = [-120.9337831731634, 45.32236865268924; -120.9207831731632, 45.32236865268924; -120.9207831731632, 45.32736865268914; -120.93378317316344, 45.32736865268914];
dist_arr = zeros(1, length(zones));
if ~isempty(dist_arr)
    for i = 1:length(T)
        pt = [X(i, 3), X(i,2)];
        for z = 1:length(zones)
            [shortest_dist_to_poly, ~] = distance_from_pt_to_polygon(zones{z}, pt);
            if is_pt_in_poly( zones{z}, pt )
                shortest_dist_to_poly = -shortest_dist_to_poly;
            end
            dist_arr(z) = shortest_dist_to_poly;
        end
        X(i, size_of_a_record+1) = min(dist_arr);

        pt = [X(i, 7), X(i,6)];
        for z = 1:length(zones)
            [shortest_dist_to_poly, ~] = distance_from_pt_to_polygon(zones{z}, pt);
            if is_pt_in_poly( zones{z}, pt )
                shortest_dist_to_poly = -shortest_dist_to_poly;
            end
            dist_arr(z) = shortest_dist_to_poly;
        end
        X(i, size_of_a_record+2) = min(dist_arr);
        
        pt = [X(i, 11), X(i,10)];
        for z = 1:length(zones)
            [shortest_dist_to_poly, ~] = distance_from_pt_to_polygon(zones{z}, pt);
            if is_pt_in_poly( zones{z}, pt )
                shortest_dist_to_poly = -shortest_dist_to_poly;
            end
            dist_arr(z) = shortest_dist_to_poly;
        end
        X(i, size_of_a_record+3) = min(dist_arr);

        for t_i = 1:length(taskMonitoringResults)
            X(i, size_of_a_record+3+t_i) = taskMonitoringResults{t_i}(3);
        end
    end
end

trajectories{end+1} = X;
X = X(:, 2:end);
end

