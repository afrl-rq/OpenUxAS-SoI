function pid = getpidof_java(task)
% Returns the process id for a java process.
    [response, tasks] = system(sprintf('jps -v | grep "%s"', task));

    splits = regexp(tasks, ' *', 'split');

    pid = str2double(splits{1});

end