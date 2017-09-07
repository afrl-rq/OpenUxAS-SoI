

%% User Settings:
% MESSAGES_TO_SEND_FOLDER = '/home/etuncali/UxAS_pulls/OpenUxAS/examples/06_Test_WaterwaySearch/MessagesToSend';
%MESSAGES_TO_SEND_FOLDER = '/home/parallels/UxAS_pulls/OpenUxAS/examples/06_Test_WaterwaySearch/MessagesToSend';
MESSAGES_TO_SEND_FOLDER = '/Users/erkan/UxASPulls/OpenUxAS/examples/07_Test_WaterwaySearch/MessagesToSend';

%% Load the blackbox script which is responsible for running the
disp(' ')
disp('This is an S-TaLiRo demo on UxAS.')
model = staliro_blackbox();
model.model_fcnptr = @uxas_blackbox;
disp(' ')
disp('Create an staliro_options object with the default options:')
opt = staliro_options();

%% Global declarations, mostly shared with the uxas_blackbox
global initCondFieldMapping;
global initCondZoneMapping;
global taskPaths;
global trajectories;
global vhcInitPositions;
global task_ids;

trajectories = cell(0);

%% Test Id Generation from the date and time:
tic;
t = datetime('now');
test_id = sprintf('%d_%d_%d_%d_%d_%d',t.Year, t.Month, t.Day, t.Hour, t.Minute, uint32(t.Second));

%% Extract Initial conditions from xml files:
[ initCondFieldMapping, xmlStruct ] = ...
        extractInitCondInformationForStaliro( MESSAGES_TO_SEND_FOLDER );

%% Extract Task Information from xml files:
taskInformation = cell(0);
taskIndices = [];
for i = 1:length(initCondFieldMapping)
    fieldType = initCondFieldMapping{i}{5};
    if strcmpi(fieldType, 'path')
        taskInformation{end+1}.fileName = initCondFieldMapping{i}{2};
        taskInformation{end}.fieldName = initCondFieldMapping{i}{3};
        taskIndices(end+1) = i;
    end
end
% Remove task related entires from the initial conditions:
rngSeedForPathGeneration = rng;
initCondFieldMapping(taskIndices) = [];
taskPaths = cell(0);
savedTaskFiles = [];
for i = 1:length(taskInformation)
    [ taskXmlStruct(i), savedTaskFiles, taskPaths{i} ] = ...
        extractPathInformationForStaliro( MESSAGES_TO_SEND_FOLDER, ...
        taskInformation{i}.fileName, taskInformation{i}.fieldName );
end

%% Extract Zone Information from xml files:
zoneInformation = cell(0);
zoneIndices = [];
for i = 1:length(initCondFieldMapping)
    fieldType = initCondFieldMapping{i}{5};
    if strcmpi(fieldType, 'zone')
        zoneInformation{end+1}.fileName = initCondFieldMapping{i}{2};
        zoneInformation{end}.fieldName = initCondFieldMapping{i}{3};
        zoneIndices(end+1) = i;
    end
end
% Remove zone related entires from the initial conditions:
rngSeedForZoneGeneration = rng;
initCondFieldMapping(zoneIndices) = [];
taskZones = cell(0);
for i = 1:length(zoneInformation)
    [ initCondZoneMapping(i).xmlStruct, ...
        initCondZoneMapping(i).fileName, ...
        initCondZoneMapping(i).polyVertices ] = ...
        extractZoneInformationForStaliro( MESSAGES_TO_SEND_FOLDER, ...
        zoneInformation{i}.fileName, zoneInformation{i}.fieldName );
end

%% Read Task ID
task_ids = extractTaskInformationForStaliro( MESSAGES_TO_SEND_FOLDER );

%% Extract vehicle initial positions. This will be used for checking if a randomly
%% placed KeepOut zone intersects with the initial positions of the aircraft.
vhcInitPositions = extractInitVhcPositionInformation( MESSAGES_TO_SEND_FOLDER );

%% Set Initial Conditions for s-taliro
disp(' ')
disp('The constraints on the initial conditions defined as a hypercube:')
init_cond = [];
for i = 1:length(initCondFieldMapping)
    init_cond = [init_cond; initCondFieldMapping{i}{4}];
end

%% Add the task area into the init_cond as the range for KeepOut zone position.
if ~isempty(initCondZoneMapping)
    start_end_pts = [];
    if ~isempty(taskPaths)
        start_end_pts = zeros(2*length(taskPaths), length(taskPaths{1}(1, :)));
        for p_ind = 1:length(taskPaths)
            pt_arr = taskPaths{p_ind};
            start_end_pts(2*p_ind-1, :) = pt_arr(1, :);
            start_end_pts(2*p_ind, :) = pt_arr(end, :);
        end
        areaBoundaries.x_min = min(start_end_pts(:, 2));
        areaBoundaries.x_max = max(start_end_pts(:, 2));
        areaBoundaries.y_min = min(start_end_pts(:, 1));
        areaBoundaries.y_max = max(start_end_pts(:, 1));
    end
    for i = 1:length(initCondZoneMapping)
        bounds = [areaBoundaries.x_min, areaBoundaries.x_max; ...
            areaBoundaries.y_min, areaBoundaries.y_max];
        init_cond = [init_cond; bounds];
    end
end

%% Metric Temporal Logic Requirement Specifications:
disp(' ')
disp('The specification:')

% Requirements:
% Whenever a vehicle goes into keep out zone, it should get out in 20
% seconds AND task robustness has to be larger than 0 (task completed).
phi = '([]((!r1 -> <>_[0, 5]r1) /\ [](!r2 -> <>_[0, 5]r2) /\ [](!r3 -> <>_[0, 5]r3)))' 

% Requirement r1
ii = 1;
preds(ii).str='r1';
preds(ii).A = [0 0 0 0 0 0 0 0 0 0 0 0 -1 0 0 0];
preds(ii).b = 0;
preds(ii).loc = [];

% Requirement r2
ii = ii+1;
preds(ii).str='r2';
preds(ii).A = [0 0 0 0 0 0 0 0 0 0 0 0 0 -1 0 0];
preds(ii).b = 0;
preds(ii).loc = [];

% Requirement r3
ii = ii+1;
preds(ii).str='r3';
preds(ii).A = [0 0 0 0 0 0 0 0 0 0 0 0 0 0 -1 0];
preds(ii).b = 0;
preds(ii).loc = [];

% Requirement r4
ii = ii+1;
preds(ii).str='r4';
preds(ii).A = [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 -1];
preds(ii).b = 0;
preds(ii).loc = [];

% Requirements are over state space (X):
opt.spec_space = 'X';

%% Maximum Simulation Duration
disp(' ')
disp('Total Simulation time:')
time = 250

%% Other s-taliro parameters
disp(' ')
disp('The constraints on the input signal defined as a range:')
input_range = [];
disp(' ')
disp('The number of control points for the input signal:')
cp_array = [];

disp(' ')
disp('Change options:')
% How many tests will start:
opt.runs = 1;
% Max number of simulations per test:
n_tests = 100;
% opt.optim_params.n_tests = n_tests;
opt.interpolationtype = {};
opt.dispinfo = 1;
% Stochastic optimization method:

opt

%% Execute s-taliro


opt.optimization_solver = 'SA_Taliro';
opt.optim_params.n_tests = n_tests;
disp('Running S-TaLiRo with Simulated Annealing...')
[results, history, opt] = staliro(model,init_cond,input_range,cp_array,phi,preds,time,opt);

%% Save initial conditions to xml files so that the tests can be repeated:
runtime=toc;

disp('Saving xml files ...')
savedInitCondFiles = cell(0);
for i = 1:length(results.run)
    savedInitCondFiles{i}.files = write_init_cond_back_to_xml(MESSAGES_TO_SEND_FOLDER, ...
            [test_id, '_run_', num2str(i)], results.run(1).bestSample ,initCondFieldMapping);
end

%% Generate test results report
disp('Generating S-TaLiRo test results report...')
save(['../staliro_reports/', test_id, '_test.mat']);
save_staliro_report;

runtime



