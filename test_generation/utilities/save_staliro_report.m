staliro_test_report = [];
staliro_test_report.test_id = test_id;
staliro_test_report.requirements_spec = strrep(phi,'\','\\');
staliro_test_report.matlab_report_file.Text = ['''', test_id, '_test.mat'''];
staliro_test_report.num_of_runs = opt.runs;
staliro_test_report.num_of_tests = n_tests;
staliro_test_report.simulation_time = time;
staliro_test_report.messages_to_send_folder = MESSAGES_TO_SEND_FOLDER;
if isempty(savedTaskFiles)
    staliro_test_report.used_task_files = ' ';
end
for i = 1:length(savedTaskFiles)
    staliro_test_report.used_task_files.task_file{i}.name.Text = [savedTaskFiles{i}];
    path_image_file = [pwd(),'/../staliro_reports/',test_id,'_task_', num2str(i), '_path.png'];
    f = plot_path2d(taskPaths{i}, false);
    saveas(f, path_image_file);
    staliro_test_report.used_task_files.task_file{i}.path_image_file.Text = path_image_file;
end

if length(savedInitCondFiles) ~= length(results.run)
    staliro_test_report.init_cond_files = ' ';
else
    for r = 1:length(results.run)
        for i = 1:length(savedInitCondFiles{r}.files)
            staliro_test_report.init_cond_files.init_cond_file{r}.files{i}.name.Text = [savedInitCondFiles{r}.files{i}];
            staliro_test_report.init_cond_files.init_cond_file{r}.files{i}.run = r;
        end
    end
end

if isempty(initCondFieldMapping)
    staliro_test_report.initial_conditions = ' ';
end
for i = 1:length(initCondFieldMapping)
    staliro_test_report.initial_conditions.init_cond{i}.index = initCondFieldMapping{i}{1};
    staliro_test_report.initial_conditions.init_cond{i}.file_name = initCondFieldMapping{i}{2};
    staliro_test_report.initial_conditions.init_cond{i}.field_name = initCondFieldMapping{i}{3};
    staliro_test_report.initial_conditions.init_cond{i}.minimum_value = initCondFieldMapping{i}{4}(1);
    staliro_test_report.initial_conditions.init_cond{i}.maximum_value = initCondFieldMapping{i}{4}(2);
end

for i = 1:length(results.run)
    if results.run(i).falsified == 0
        staliro_test_report.run_reports.run{i}.is_falsified.Text = '''PASS''';
    else
        staliro_test_report.run_reports.run{i}.is_falsified.Text = '''FAIL !''';
    end
    
    staliro_test_report.run_reports.run{i}.best_robustness = results.run(i).bestRob;
    staliro_test_report.run_reports.run{i}.num_of_tests = results.run(i).nTests;
    staliro_test_report.run_reports.run{i}.execution_time = results.run(i).time;
    for j = 1:size(results.run(i).bestSample, 1)
        staliro_test_report.run_reports.run{i}.initial_condition_values.init_cond{j}.Value = results.run(i).bestSample(j,:);
        for k = 1:length(initCondFieldMapping)
            if initCondFieldMapping{k}{1} == j
                staliro_test_report.run_reports.run{i}.initial_condition_values.init_cond{j}.File = initCondFieldMapping{j}{2};
                staliro_test_report.run_reports.run{i}.initial_condition_values.init_cond{j}.Field = initCondFieldMapping{j}{3};
                break;
            end
        end
    end
end
testReportXmlStruct = [];
testReportXmlStruct.staliro_test_report.test{1} = staliro_test_report;
testReportXmlStruct.staliro_test_report.report_generation_time.Text = datestr(datetime('now'));

xmlFileName = ['../staliro_reports/', test_id, '_test.xml'];

retXml = struct2xml(testReportXmlStruct);
styleSheetText = '<?xml-stylesheet type="text/xsl" href="staliro_report_style.xsl"?>';
retXml = insertAfter(retXml, '<?xml version="1.0" encoding="utf-8"?>', styleSheetText);
fid = fopen(xmlFileName,'wt');
fprintf(fid, retXml);
fclose(fid);
%struct2xml(testReportXmlStruct, xmlFileName);
