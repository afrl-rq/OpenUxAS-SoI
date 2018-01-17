#!/usr/bin/python

# ADDS NEW SERVICE BASED ON THE SERVICE TEMPLATES FILES
# 1) run this script in the directory: 'OpenUxAS/src/Services/',
#	i.e. python 00_NewService.py
# 2) The script asks for the name of the new service
# 3) It copies the service template files, replaces the 
#	service/class names in the files, and saves the copies with
#   the new service name.
# 4) It also adds an entry in the meson.build file to include the
#	new service in the buld



def replace_words(base_text, replaceValues):
    for key, val in replaceValues.items():
        base_text = base_text.replace(key, val)
    return base_text

def main():

	newServiceName = raw_input("Enter the new service name: ")
	replaceValues = {
		'00_ServiceTemplate': newServiceName,
		'ServiceTemplate': newServiceName,
		'UXAS_00_SERVICE_TEMPLATE_H' : 'UXAS_{}_H'.format(newServiceName.upper())
	}

	fileServiceTemplate_cpp = open('00_ServiceTemplate.cpp', 'r')
	stringServiceTemplate_cpp = fileServiceTemplate_cpp.read()
	stringServiceTemplate_cpp = replace_words(stringServiceTemplate_cpp,replaceValues)
	fout = open('{0}.cpp'.format(newServiceName), 'w')
	fout.write(stringServiceTemplate_cpp)
	fout.close()

	fileServiceTemplate_h = open('00_ServiceTemplate.h', 'r')
	stringServiceTemplate_h = fileServiceTemplate_h.read()
	stringServiceTemplate_h = replace_words(stringServiceTemplate_h,replaceValues)
	fout = open('{0}.h'.format(newServiceName), 'w')
	fout.write(stringServiceTemplate_h)
	fout.close()


	headersString = '// DO NOT REMOVE - USED TO AUTOMATICALLY ADD NEW SERVICE HEADERS'
	codeString = '// DO NOT REMOVE - USED TO AUTOMATICALLY ADD NEW SERVICE DUMMY INSTANCES'
	newCodeString = '{0}\n{{auto svc = uxas::stduxas::make_unique<uxas::service::{1}>();}}'.format(codeString,newServiceName)
	replaceValues = {
		headersString : '{0}\n#include "{1}.h"'.format(headersString,newServiceName),
		codeString : newCodeString,
	}
	fileServiceList = open('00_ServiceList.h', 'r')
	stringServiceList = fileServiceList.read()
	stringServiceList = replace_words(stringServiceList,replaceValues)
	fout = open('00_ServiceList.h', 'w')
	fout.write(stringServiceList)
	fout.close()

	srcsString = 'srcs_services = ['
	newSrcsString = '{0}\n\t\'{1}.cpp\','.format(srcsString,newServiceName)
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
