
BinPath = bin
GluPath = glu-2.4

.PHONY: all
all: $(GluPath)/libglu.a $(BinPath)/protocon

.PHONY: $(BinPath)/protocon
$(BinPath)/protocon:
	$(MAKE) -C protocon all


$(GluPath)/configure:
	git submodule init $(GluPath)
	git submodule update $(GluPath)

$(GluPath)/Makefile: $(GluPath)/configure
	cd $(GluPath) && ./configure --enable-gcc

$(GluPath)/libglu.a: $(GluPath)/Makefile
	cd $(GluPath) && make

.PHONY: clean
clean:
	$(MAKE) -C protocon clean

.PHONY: tags
tags:
	find -type f \
		-not -path '*/.*' \
		-not -path '*/html/*' -not -path '*/bld/*' \
		-not -path './bin/*' \
		-not -path './doc/*' \
		-not -path './$(GluPath)/src/*' \
		'(' -name '*.h' -or -name '*.c' -or -name '*.cc' -or -name '*.hh' ')' \
		-prune \
		| \
		ctags -L -

.PHONY: update
update:
	git pull origin master

