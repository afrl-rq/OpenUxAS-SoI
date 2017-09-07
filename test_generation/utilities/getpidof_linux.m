function pid = getpidof_linux(task)
% Returns the process id for a unix process.
    [response, tasks] = system(sprintf('ps -ef | grep "%s"', task));

    splits = regexp(tasks, ' *', 'split');

    pid = str2double(splits{2});

end