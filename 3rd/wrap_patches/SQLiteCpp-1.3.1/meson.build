project('sqlitecpp', 'cpp')

dep_sqlite3 = dependency(
  'sqlite3',
  fallback: ['sqlite3', 'dep'],
)

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
  dependencies: dep_sqlite3,
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
