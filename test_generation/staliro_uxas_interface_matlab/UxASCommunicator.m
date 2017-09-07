classdef UxASCommunicator
    % A class to handle communications with UxAS.
    properties
        port
        server
        sock
    end
    
    properties (Constant)
        STALIRO_INIT_COND = 1;
        STALIRO_INPUT_SIG = 2;
        STALIRO_START_SIM = 3;
        STALIRO_ACK = 4;
        STALIRO_NAK = 5;
        STALIRO_TRAJ_INFO = 10;
        STALIRO_TRAJ_DATA = 11;
        STALIRO_REQUEST_TRAJECTORY = 12;
        STALIRO_HEART_BEAT = 20;
        STALIRO_END_OF_SIMULATION = 21;
        STALIRO_TASK_STATUS = 22;
        
        UXAS_SOCK_TIMEOUT = 20;
    end
    methods
        function obj = UxASCommunicator(server, port)
            obj.port = 10020;
            obj.server = '127.0.0.1';
            if nargin > 1
                if isnumeric(port)
                    obj.port = port;
                else
                    error('UxASCommunicator: Server port must be numeric')
                end
            end
            if nargin > 0
                if isstr(server)
                    obj.server = server;
                else
                    error('UxASCommunicator: Server address must be string')
                end
            end
            obj.sock = tcpip(obj.server, obj.port);%, 'NetworkRole', 'client');
            obj.sock.ByteOrder = 'littleEndian';
            obj.sock.OutputBufferSize = 640000;
        end
        
        function stat = connect(self)
            try
                info_str = sprintf('Connecting to %s:%d...', self.server, self.port);
                fopen(self.sock);
                pause(0.1);
                stat = self.sock.status;
                info_str = [info_str, stat, '\n'];
                self.sock.timeout = self.UXAS_SOCK_TIMEOUT;
                fprintf(info_str);
            catch
                stat = self.sock.status;
                error('Could not connect!');
            end
        end
        
        function disconnect(self)
            fclose(self.sock);
            delete(self.sock);
            clear self.sock
        end
        
        function sendMsg(self, msg)
            len = length(msg);
            fwrite(self.sock, [typecast(uint32(len), 'uint8'), msg], 'uint8');
        end
        
        function sendCmd(self, cmd)
            fwrite(self.sock, [typecast(uint32(cmd), 'uint8')], 'uint8');
        end
        
        function sendSimDuration(self, simDuration)
            fwrite(self.sock, [typecast(double(simDuration), 'uint8')], 'uint8');
        end
        
        function ack = getACK(self)
            try
                [ack, num_read] = fread(self.sock, 1, 'uint32');
                if num_read ~= 1
                    fprintf('getACK read: %d numbers\n', num_read);
                    ack = 0;
                end
            catch
                ack = 0;
                error('getACK: Can not read!');
            end
        end
        
        function [success, num] = receiveUint32(self)
            success = true;
            try
                [num, num_read] = fread(self.sock, 1, 'uint32');
                if num_read ~= 1
                    fprintf('receiveUint32 read: %d numbers\n', num_read);
                    success = false;
                end
            catch
                num = 0;
                success = false;
                error('receiveUint32: Can not read!');
            end
        end
        
        function [success, num] = receiveInt32(self)
            success = true;
            try
                [num, num_read] = fread(self.sock, 1, 'int32');
                if num_read ~= 1
                    fprintf('receiveInt32 read: %d numbers\n', num_read);
                    success = false;
                end
            catch
                num = 0;
                success = false;
                error('receiveInt32: Can not read!');
            end
        end
          
        function ack = sendInitCond(self, initCond, initCondFieldMapping)
            ack = -1;
            for i = 1:length(initCondFieldMapping)
                self.sendCmd(self.STALIRO_INIT_COND);
                self.sendMsg(initCondFieldMapping{i}{2});
                % UxAS side is looking for dots instead of {,} for indices:
                tempStr = strrep(initCondFieldMapping{i}{3},'{','.');
                tempStr = strrep(tempStr,'}','.');
                self.sendMsg(tempStr);
                self.sendMsg(num2str(initCond(initCondFieldMapping{i}{1})));
                ack = self.getACK();
            end
        end
        
        function ack = startSim(self, simDuration)
            self.sendCmd(self.STALIRO_START_SIM);
            self.sendSimDuration(simDuration);
            ack = self.getACK();
        end
        
        function requestTrajectory(self)
            self.sendCmd(self.STALIRO_REQUEST_TRAJECTORY)
        end
        
        function [traj, listOfVehiclesAndIndices] = receiveTrajectory(self)
            self.requestTrajectory()
            self.sock.timeout = self.UXAS_SOCK_TIMEOUT;
            [numColumns, numRows, listOfVehiclesAndIndices] = self.receiveTrajectoryInfo();
            traj = self.receiveTrajectoryData(numColumns, numRows);
        end
        
        function [isEndOfSimulation, cur_sim_time, total_sim_time] = receiveSimulationStatus(self)
            simStatReceived = 0;
            isEndOfSimulation = 0;
            cur_sim_time = 0;
            total_sim_time = 1;
            while simStatReceived == 0
                [success, cmd] = self.receiveUint32();
                if success && cmd == self.STALIRO_HEART_BEAT
                    [hbArr, rcvSuccess] = self.receiveDoubles(2);
                    if rcvSuccess
                        fprintf(repmat('\b', 1, 18));
                        %if ~simStatReceived
                        %    fprintf('%s','Simulation Status: ');
                            simStatReceived = 1;
                        %end
                        fprintf('%8.2f/%8.2f', hbArr(1), hbArr(2));
                        cur_sim_time = hbArr(1);
                        total_sim_time = hbArr(2);
                    end
                elseif success && cmd == self.STALIRO_END_OF_SIMULATION
                    simStatReceived = 1;
                    isEndOfSimulation = 1;
                else
                    success
                    cmd
                    error('can not read uint32');
                end
            end
            fprintf('\n');
        end
        
        function [isEndOfSimulation, task_id, task_status, task_robustness] = receiveTaskStatus(self)
            isEndOfSimulation = 0;
            task_id = 0;
            task_status = 0;
            task_robustness = 0.0;
            received = 0;
            fprintf('Will receive task status!\n');
            while received == 0
                [success, cmd] = self.receiveUint32();
                if success && cmd == self.STALIRO_TASK_STATUS
                    [rcvSuccess, task_id] = self.receiveInt32();
                    if rcvSuccess
                        [rcvSuccess, task_status] = self.receiveInt32();
                        if rcvSuccess
                            [task_robustness, rcvSuccess] = self.receiveDoubles(1);
                            if rcvSuccess
                                received = 1;
                            end
                        end
                    end
                elseif success && cmd == self.STALIRO_END_OF_SIMULATION
                    isEndOfSimulation = 1;
                    received = 1;
                else
                    success
                    cmd
                    error('!!! Can not read task status');
                end
            end
            fprintf('\n - task status ok\n');
        end
        
        function [numColumns, numRows, listOfVehiclesAndIndices] = receiveTrajectoryInfo(self)
            trajInfoReceived = 0;
            simStatReceived = 0;
            listOfVehiclesAndIndices = [];
            fprintf('Will receive trajectory info!\n')
            while trajInfoReceived == 0
                [success, cmd] = self.receiveUint32();
                if success && cmd == self.STALIRO_TRAJ_INFO
                    trajInfoReceived = 1;
                    [success, num] = self.receiveUint32();
                    if success
                        numColumns = num;
                        [success, num] = self.receiveUint32();
                        if success
                            numRows = num;
                            [success, num] = self.receiveUint32();
                            if success
                                numVehicles = num;
                                for i = 1:numVehicles
                                    [success, vehicle_id] = self.receiveUint32();
                                    if success
                                        [success, vehicle_index] = self.receiveUint32();
                                        if success
                                            vehicle_and_index = [vehicle_id, vehicle_index];
                                            listOfVehiclesAndIndices(end+1, :) = vehicle_and_index;
                                        end
                                    end
                                end
                                self.sendCmd(self.STALIRO_ACK);
                            end
                        end
                    end
                elseif success && cmd == self.STALIRO_HEART_BEAT
                    [hbArr, rcvSuccess] = self.receiveDoubles(2);
                    if rcvSuccess
                        if ~simStatReceived
                            fprintf('%s','Simulation Status: ');
                            simStatReceived = 1;
                        else
                            fprintf(repmat('\b',1,17));
                        end
                        fprintf('%8.2f/%8.2f', hbArr(1), hbArr(2));
                    end
                else
                    success
                    cmd
                    error('!!! Can not read uint32');
                end
            end
            fprintf('\n - trajectory info ok.\n');
        end
      
        function [dblArr, success] = receiveDoubles(self, numDoubles)
            success = 0;
            dblArr = [];
            totalRead = 0.0;
            while totalRead < numDoubles
                [tmpArr, num_read] = fread(self.sock, numDoubles-totalRead, 'double');
                if num_read > 0
                    dblArr = [dblArr; tmpArr];
                    totalRead = totalRead + num_read;
                else
                    error('!!! Can not read doubles');
                end
            end
            if totalRead == numDoubles
                success = 1;
            end
        end
        
        function [traj] = receiveTrajectoryData(self, numColumns, numRows)
            totalExpected = numColumns*numRows;
            totalReceived = 0;
            dblArr = [];
            
            fprintf('Will receive trajectory data!\n');
            while totalReceived < totalExpected
                [success, cmd] = self.receiveUint32();
                if success && cmd == self.STALIRO_TRAJ_DATA
                    [success, numBytes] = self.receiveUint32();
                    if success
                        numDoubles = numBytes / 8;
                        [tmpArr, success] = self.receiveDoubles(numDoubles);
                        if success
                            dblArr = [dblArr; tmpArr];
                            totalReceived = totalReceived + numDoubles;
                            self.sendCmd(self.STALIRO_ACK);
                        end
                    end
                end
            end
            traj = reshape(dblArr, numColumns, numRows);
            traj = traj';
            fprintf(' - trajectory data ok!\n');
        end
        
        function [rob, success] = getRobustness(self)
            success = 0;
            rob = 1000000;
            self.sock.timeout = self.UXAS_SOCK_TIMEOUT;
            [rob, num_read] = fread(self.sock, 1, 'double');
            if num_read > 0
                success = 1;
            else
                fprintf('Robustness read: %d\n', num_read);
            end
        end
        
        function msg = createMsgSignal(self, signalDesc)
            msg(1) = uint8(signalDesc.signalType);
            msg(2) = uint8(signalDesc.interpType);
            msg(3) = uint8(signalDesc.signalRefIndex);
            msg(4) = uint8(signalDesc.signalRefField);
            msg = [msg, typecast(uint16(length(signalDesc.signalVals)), 'uint8')];
            msg = [msg, typecast(signalDesc.signalVals, 'uint8')];
            msg = [msg, typecast(signalDesc.refVals, 'uint8')];
        end

    end
end
