project('sqlitecpp', 'cpp')

lib = static_library('sqlitecpp', [
	'src/Backup.cpp',
	'src/Column.cpp',
	'src/Database.cpp',
	'src/Statement.cpp',
	'src/Transaction.cpp',
	],
	cpp_args: [
		'-std=c++11',
	],
	include_directories: include_directories(
		'include',
                '../sqlite-amalgamation-3120200',
	),
)
