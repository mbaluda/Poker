RM=rm -Rf
CXX=g++
CXXFLAGS=-W -Wall -ansi -pedantic -g
LDFLAGS=-lcppunit

EXE=poker

DOC=doxygen
DOC_FILES=doc poker.tag

all: ${EXE}

${EXE}: ${EXE}.cpp
	$(CXX) $(CXXFLAGS) -o ${EXE} $<

doc:
	$(DOC)

clean:
	$(RM) $(EXE) $(TEST_EXE) $(DOC_FILES)