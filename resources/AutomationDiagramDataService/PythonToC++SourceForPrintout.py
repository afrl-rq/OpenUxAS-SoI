#! /usr/bin/env python

def Convert(baseFile):
	pythonFile = baseFile + '.py'
	cppFile = open(baseFile + '.code','w')
	with open(pythonFile) as pFile:
	    for line in pFile:
	       replaceLine = line.replace('\n','')
	       replaceLine = replaceLine.replace('\"','\'')
	       replaceLine = replaceLine.replace('\t','\\t')
	       replaceLine = replaceLine.replace('\\d+','\\\\d+')

	       newLine = 'file << \"' + replaceLine + '\" << std::endl;\n'
	       cppFile.write(newLine)
	cppFile.close()

def main():

	Convert('PlotAutomationDiagram')
	Convert('ProcessTasks')
	Convert('ProcessUniqueAutomationResponse')
	Convert('ProcessEntityStates')
	Convert('ProcessZones')

if __name__ == '__main__':
	main()
