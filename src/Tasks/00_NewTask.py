#!/usr/bin/python

# ADDS NEW TASK BASED ON THE TASK TEMPLATES FILES
# 1) run this script in the directory: 'OpenUxAS/src/Tasks/',
#	i.e. python 00_NewTask.py
# 2) The script asks for the name of the new Task
# 3) It copies the Task template files, replaces the 
#	Task/class names in the files, and saves the copies with
#   the new Task name.
# 4) It also adds an entry in the meson.build file to include the
#	new Task in the buld



def replace_words(base_text, replaceValues):
    for key, val in replaceValues.items():
        base_text = base_text.replace(key, val)
    return base_text

def main():

	newTaskName = raw_input("Enter the new Task name: ")
	replaceValues = {
		'00_TaskTemplate': newTaskName,
		'TaskTemplate': newTaskName,
		'UXAS_00_TASK_TEMPLATE_H' : 'UXAS_TASK_{}_H'.format(newTaskName.upper())
	}

	fileTaskTemplate_cpp = open('00_TaskTemplate.cpp', 'r')
	stringTaskTemplate_cpp = fileTaskTemplate_cpp.read()
	stringTaskTemplate_cpp = replace_words(stringTaskTemplate_cpp,replaceValues)
	fout = open('{0}.cpp'.format(newTaskName), 'w')
	fout.write(stringTaskTemplate_cpp)
	fout.close()

	fileTaskTemplate_h = open('00_TaskTemplate.h', 'r')
	stringTaskTemplate_h = fileTaskTemplate_h.read()
	stringTaskTemplate_h = replace_words(stringTaskTemplate_h,replaceValues)
	fout = open('{0}.h'.format(newTaskName), 'w')
	fout.write(stringTaskTemplate_h)
	fout.close()


	headersString = '// DO NOT REMOVE - USED TO AUTOMATICALLY ADD NEW TASK HEADERS'
	codeString = '// DO NOT REMOVE - USED TO AUTOMATICALLY ADD NEW TASK DUMMY INSTANCES'
	newCodeString = '{0}\n{{auto svc = uxas::stduxas::make_unique<uxas::service::task::{1}>();}}'.format(codeString,newTaskName)
	replaceValues = {
		headersString : '{0}\n#include "{1}.h"'.format(headersString,newTaskName),
		codeString : newCodeString,
	}
	fileTaskList = open('../Services/00_ServiceList.h', 'r')
	stringTaskList = fileTaskList.read()
	stringTaskList = replace_words(stringTaskList,replaceValues)
	fout = open('../Services/00_ServiceList.h', 'w')
	fout.write(stringTaskList)
	fout.close()

	srcsString = 'srcs_tasks = ['
	newSrcsString = '{0}\n\t\'{1}.cpp\','.format(srcsString,newTaskName)
	replaceValues = {
		srcsString : newSrcsString,
	}
	fileMesonBuild = open('meson.build', 'r')
	stringMesonBuild = fileMesonBuild.read()
	stringMesonBuild = replace_words(stringMesonBuild,replaceValues)
	fout = open('meson.build', 'w')
	fout.write(stringMesonBuild)
	fout.close()






if __name__ == '__main__':
    main()
