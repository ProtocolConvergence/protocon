
CXX = g++

CONFIG += ansi
#CONFIG += errwarn
CONFIG += debug
#CONFIG += ultradebug
#CONFIG += fast
#CONFIG += noassert

BinPath = ../bin
GluPath = ../glu-2.4
GluIncludePath = $(GluPath)/include

IXXFLAGS += -I$(GluPath)/include
LXXFLAGS += -L$(GluPath) -lcmu -lglu -lcu -lcal -lm

ifneq (,$(filter debug,$(CONFIG)))
	CXXFLAGS += -g
endif
ifneq (,$(filter ultradebug,$(CONFIG)))
	CXXFLAGS += -g3
endif
ifneq (,$(filter fast,$(CONFIG)))
	CXXFLAGS += -O3
endif
ifneq (,$(filter noassert,$(CONFIG)))
	CXXFLAGS += -DNDEBUG
endif
ifneq (,$(filter ansi,$(CONFIG)))
	CXXFLAGS += -ansi -pedantic
endif
ifneq (,$(filter errwarn,$(CONFIG)))
	CXXFLAGS += -Werror
endif

CXXFLAGS += -Wall -Wextra -Wstrict-aliasing

all: $(BinPath)/protocon

$(BinPath)/protocon: main.o synhax.o xnsys.o
	$(CXX) $(CXXFLAGS) $^ -o $@ $(LXXFLAGS)

%.o: %.cc
	$(CXX) $(CXXFLAGS) $(IXXFLAGS) -c $< -o $@

main.o: pf.hh set.hh xnsys.hh

$(BinPath)/protocon: | $(BinPath)

$(BinPath):
	mkdir -p $@

.PHONY: clean
clean:
	rm -f *.o $(BinPath)/protocon

