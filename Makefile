
BldPath=bld
BinPath=bin

SrcPath=src
DepPath=dep
CxTopPath=$(DepPath)/cx
MddGluPath=$(DepPath)/mdd-glu

ScanBldPath=clang
ScanRptPath=$(ScanBldPath)/report
SCAN_BUILD=scan-build -o $(PWD)/$(ScanRptPath)

CMakeExe=cmake
CMAKE=$(CMakeExe)
GODO=$(CMakeExe) -E chdir
MKDIR=$(CMakeExe) -E make_directory
CTAGS=ctags

.PHONY: default all release cmake proj \
	test analyze tags \
	clean-analyze clean distclean \
	dep \
	init update pull

default:
	$(MAKE) init
	if [ ! -d $(BldPath) ] ; then $(MAKE) cmake ; fi
	$(MAKE) proj

all:
	$(MAKE) init
	$(MAKE) cmake
	$(MAKE) proj


release:
	$(MAKE) CMAKE="$(CMakeExe) -D CMAKE_BUILD_TYPE:string=RELEASE" cmake
	$(MAKE) CMAKE="$(CMakeExe) -D CMAKE_BUILD_TYPE:string=RELEASE" proj

snappy:
	$(MAKE) CMAKE="$(CMakeExe) -D CMAKE_BUILD_TYPE:string=RelWithDebInfo" cmake
	$(MAKE) CMAKE="$(CMakeExe) -D CMAKE_BUILD_TYPE:string=RelWithDebInfo" proj

debug:
	$(MAKE) CMAKE="$(CMakeExe) -D CMAKE_BUILD_TYPE:string=DEBUG" cmake
	$(MAKE) CMAKE="$(CMakeExe) -D CMAKE_BUILD_TYPE:string=DEBUG" proj


cmake:
	if [ ! -d $(BldPath) ] ; then $(MKDIR) $(BldPath) ; fi
	$(GODO) $(BldPath) $(CMAKE) ..

proj:
	$(GODO) $(BldPath) $(MAKE)

test:
	$(GODO) $(BldPath) $(MAKE) test

analyze:
	rm -fr $(ScanRptPath)
	$(MAKE) 'BldPath=$(ScanBldPath)' 'CMAKE=$(SCAN_BUILD) cmake' 'MAKE=$(SCAN_BUILD) make'

tags:
	$(CTAGS) -R src -R dep/cx/src

clean-analyze:
	rm -fr $(ScanBldPath)

clean:
	$(GODO) $(BldPath) $(MAKE) clean

distclean:
	$(GODO) $(CxTopPath) $(MAKE) distclean || true
	rm -fr $(MddGluPath)/bld
	rm -fr $(BldPath) $(BinPath) $(ScanBldPath) tags

dep:
	$(GODO) $(CxTopPath) $(MAKE)

init:
	if [ ! -f $(DepPath)/cx/src/cx.c ] ; then git submodule init dep/cx ; git submodule update dep/cx ; fi
	if [ ! -f $(DepPath)/cx-pp/cx.c ] ; then git submodule init dep/cx-pp ; git submodule update dep/cx-pp ; fi
	if [ ! -f $(DepPath)/mdd-glu/README ] ; then git submodule init dep/mdd-glu ; git submodule update dep/mdd-glu ; fi

update:
	git pull origin trunk
	git submodule update
	git -C dep/cx checkout master
	git -C dep/cx merge --ff-only origin/master
	git -C dep/cx-pp checkout master
	git -C dep/cx-pp merge --ff-only origin/master
	git -C dep/mdd-glu checkout master
	git -C dep/mdd-glu merge --ff-only origin/master

pull:
	git pull origin trunk
	git -C dep/cx pull origin master
	git -C dep/cx-pp pull origin master
	git -C dep/mdd-glu pull origin master
	if [ -d $(DepPath)/tex2web ] ; then $(GODO) $(DepPath)/tex2web git pull origin master ; fi

