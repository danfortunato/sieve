CXX = g++
CXXFLAGS = -g

SRCDIR = lib
SRCEXT = cpp
SOURCES = $(shell find $(SRCDIR) -type f -name *.$(SRCEXT) -depth 1)

TESTDIR = test
TESTSRC = main
TEST = $(TESTDIR)/$(TESTSRC).$(SRCEXT)

SRCINCDIR = $(SRCDIR)/include
SRCINC = -I $(SRCINCDIR)
INCDIR = include
INC = -I $(INCDIR)

BUILDDIR = build
TARGETDIR = .
TARGET = $(TARGETDIR)/a.out

OBJECTS = $(patsubst $(SRCDIR)/%,$(BUILDDIR)/%,$(SOURCES:.$(SRCEXT)=.o))
OBJECTS += $(patsubst $(TESTDIR)/%,$(BUILDDIR)/%,$(TEST:.$(SRCEXT)=.o))

.PHONY: test
test: $(TARGET)

$(TARGET): $(OBJECTS)
	@mkdir -p $(TARGETDIR)
	$(CXX) $^ -o $(TARGET)

$(BUILDDIR)/$(TESTSRC).o: $(TEST)
	@mkdir -p $(BUILDDIR)
	$(CXX) $(CXXFLAGS) $(INC) $(SRCINC) -c -o $@ $<

$(BUILDDIR)/%.o: $(SRCDIR)/%.$(SRCEXT)
	@mkdir -p $(BUILDDIR)
	$(CXX) $(CXXFLAGS) $(SRCINC) -c -o $@ $<

.PHONY: clean
clean:
	@rm -rf $(BUILDDIR)
	@rm $(TARGET)

Makefile: ;
	