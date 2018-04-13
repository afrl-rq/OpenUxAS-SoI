project('sqlitecpp', 'cpp')

dep_sqlite3 = dependency(
  'sqlite3',
  required: false,
)

# force native build of SQLite3 if load extension function is unavailable
cpp = meson.get_compiler('cpp')
if not dep_sqlite3.found() or not cpp.has_function('sqlite3_enable_load_extension', dependencies: dep_sqlite3)
  dep_sqlite3 = subproject('sqlite3').get_variable('dep')
endif


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
