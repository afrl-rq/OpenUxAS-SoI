SRCFILES=main.cpp

CC=g++

CFLAGS=-DLINUX -std=c++11 -Wall

LDFLAGS=-static

SRC=$(SRCFILES)

LIBS=-L../../../build/src/LMCP
LIBS+=-llmcp

INCS=-I../../../src/LMCP 

OBJ=$(SRC:.cpp=.o)

EXE=ext_logger

RM=rm -f

.PHONY: all 
.PHONY: clean
.PHONY: invoker 

all: $(LIB) $(EXE)

exe: $(EXE)
	
%.o: %.cpp 
	$(CC) $(CFLAGS) $(INCS) -o $@ -c $<

$(EXE): $(OBJ)
	$(CC) $(OBJ) -o $@ $(LDFLAGS) $(LIBS)

clean: 
	-$(RM) $(OBJ) $(EXE)
