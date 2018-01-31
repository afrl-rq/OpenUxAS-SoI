project('sqlitecpp', 'cpp')

lib = static_library(
  'sqlitecpp',
  [
    'src/Backup.cpp',
    'src/Column.cpp',
    'src/Database.cpp',
    'src/Statement.cpp',
    'src/Transaction.cpp',
  ],
  cpp_args: [
    '-std=c++11',
  ],
  dependencies: subproject('sqlite3').get_variable('dep'),
  include_directories: include_directories(
    'include',
  ),
)

dep = declare_dependency(
  link_with: lib,
  include_directories: include_directories(
    'include',
  ),
)
