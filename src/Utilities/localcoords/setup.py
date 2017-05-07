from distutils.core import setup, Extension

module1 = Extension('LocalCoords',sources=['LocalCoordsModule.cpp',
                                           '../UnitConversions.cpp'],
					extra_compile_args=['-std=c++11','-DLINUX'],
                    include_dirs=['.', '../../Includes'])

setup (name = 'LocalCoords',
       version = '1.0',
       description = 'This package converts between Lat Lon and meters from an origin',
       ext_modules = [module1])
