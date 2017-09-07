function [ traj ] = UxASInterface( initCond, initCondFieldMapping, simDuration )
%UxASInterface Summary of this function goes here
%   Detailed explanation goes here

orgDir = pwd;
cd('/home/etuncali/UxAS_pulls/OpenUxAS/examples/06_Test_WaterwaySearch');
system('./runUxAS_WaterwaySearch.sh&');
pause(1);

traj = [];
uxasCom = UxASCommunicator('127.0.0.1', 5556);
connectTryCount = 0;
while strcmpi(uxasCom.sock.Status, 'closed')
    uxasCom.connect();
    pause(0.1);
    connectTryCount = connectTryCount + 1;
    if connectTryCount > 300
        break;
    end
end
if strcmpi(uxasCom.sock.Status, 'open')
    disp('Connected to UxAS.');
    ack = uxasCom.sendInitCond(initCond, initCondFieldMapping);
    disp('Sent init cond.');
    %pause(1);
    system('./runAMASE_WaterwaySearch_headless.sh&');
    ack = uxasCom.startSim(simDuration);
    disp('Started Simulation... (Waiting for the trajectory)');
    pause(1);
    traj = uxasCom.receiveTrajectory();
    disp('Received ');
else
    disp('COULD NOT CONNECT to UxAS');
end

% TODO: Get PID of the processes started here and kill them. Following will
% kill all java
system('killall uxas');
system('killall java');
cd(orgDir);

