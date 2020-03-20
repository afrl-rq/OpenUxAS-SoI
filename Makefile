# Platform
PLATFORM:=$(shell python -c "import sys; print(sys.platform)")

# Control whether full command line should be displayed during compilation
DEBUG_BUILD=false

# Root directory in which the object and the final executable will be created
OBJECT_DIR=obj

# Source directories for the uxas project
SOURCE_DIRS:=src/Communications \
             src/Includes \
	     src/Services \
	     src/Tasks \
	     src/DPSS \
	     src/Plans \
	     src/Utilities \
	     resources/AutomationDiagramDataService \
	     src/VisilibityLib

# Compiler to be used
CXX=g++

# Default C++ compilation flags
CXX_FLAGS:=-fPIC -std=c++11

# Enable all warnings
ifeq ($(ENABLE_WARNINGS),true)
    CXX_FLAGS+=-Wall
endif

# Enable coverage with gcov
ifeq ($(ENABLE_COVERAGE),true)
    CXX_FLAGS+=-fprofile-arcs -ftest-coverage -DGCOV_MODE=1
endif

# Linker flags
ifeq ($(PLATFORM),linux)
    LINKER_FLAGS:=-std=c++11 -llmcp -lzyre -lpugixml -lboost_filesystem \
-lboost_regex -lboost_date_time -lboost_system -lSQLiteCpp -lsqlite3 \
-lczmq -luuid -lserial -lzmq -ldl -lpthread -static-libstdc++ -static-libgcc
else
    LINKER_FLAGS:=-std=c++11 -llmcp -lzyre -lpugixml -lboost_filesystem \
-lboost_regex -lboost_date_time -lboost_system -lSQLiteCpp -lsqlite3 \
-lczmq -lserial -lzmq -ldl -lpthread
endif

# Include flags
INCLUDES=$(foreach source_dir, $(SOURCE_DIRS), -I$(source_dir))

# The list of sources
SOURCES:=$(foreach source_dir, $(SOURCE_DIRS), $(wildcard $(source_dir)/*.cpp))

# The list of non relocated object files
OBJECTS_BASE:=$(patsubst %.cpp,%.o,$(SOURCES))

# The final location of all objects
OBJECTS:=$(foreach object, $(OBJECTS_BASE),$(OBJECT_DIR)/$(object))

# The list of Makefile fragments containing the dependencies
DEPS:=$(patsubst %.o,%.o.d,$(OBJECTS))

# COMPILE_CXX(object_file, source_file)
#
# Compile a C++ source and generate Makefile dependencies
#
define COMPILE_CXX
@mkdir -p `dirname $1`
@echo "[Compiling $2]"
@if test "$(DEBUG_BUILD)" = "true"; then \
    echo "$(CXX) $(CXX_FLAGS) $(INCLUDES) -MM -MT $1 $2 -MF $1.d"; \
 fi
@$(CXX) $(CXX_FLAGS) $(INCLUDES) -MM -MT $1 $2 -MF $1.d
@if test "$(DEBUG_BUILD)" = "true"; then \
    echo "$(CXX) -c $2 $(INCLUDES) $(CXX_FLAGS) -o $1"; \
 fi
@$(CXX) -c $2 $(INCLUDES) $(CXX_FLAGS) -o $1
endef

# GENERATE_COMPILER_RULE(object_file, source_file)
#
# Generate a makefile rule to compile a C++ source
#
define GENERATE_COMPILE_RULE

$(OBJECT_DIR)/$1: $2 
	$$(call COMPILE_CXX,$$@,$$<)

endef

# Toplevel targets
help:
	@echo "This makefile compiles the uxas main executable"
	@echo
	@echo "It assumes that thirdparties libraries and their respective include files"
	@echo "are available in the environment (either in the system paths or using"
	@echo "environment variables)"
	@echo
	@echo "Available targets:"
	@echo "   all:   Compile the project"
	@echo "   clean: Clean all build artefacts"
	@echo "   help:  This target"
	@echo
	@echo "User variables:"
	@echo "   DEBUG_BUILD: if 'true' then display full compilation command line"
	@echo "   OBJECT_DIR: root directory containing objects and executable (default: 'obj')"
	@echo "   ENABLE_WARNINGS: if 'true' enable all C++ warnings"
	@echo "   ENABLE_COVERAGE: if 'true' compile uxas with gcov enabled"

clean:
	@echo "[Remove objects]"
	rm -f $(OBJECTS)
	@echo "[Remove makefile fragments (dependencies)]"
	rm -f $(DEPS)

all: $(OBJECT_DIR)/uxas
	@echo "[Project compiled]"

# Main compilation and link
$(OBJECT_DIR)/uxas.o: src/UxAS_Main.cpp
	$(call COMPILE_CXX,$@,$<)

$(OBJECT_DIR)/uxas: $(OBJECT_DIR)/uxas.o $(OBJECTS)
	@echo "[Link uxas main]"
	@$(CXX) -o $@ $^ $(LINKER_FLAGS) $(CXX_FLAGS)

# Create a compilation rule for each source found
$(foreach object, $(OBJECTS_BASE), $(eval $(call GENERATE_COMPILE_RULE,$(object),$(patsubst %.o,%.cpp, $(object)))))

# Include the Makefile fragments containing the dependencies
-include $(DEPS)
