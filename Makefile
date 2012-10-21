
BinPath = bin

.PHONY: all
all: $(BinPath)/protocon

.PHONY: $(BinPath)/protocon
$(BinPath)/protocon:
	$(MAKE) -C protocon all

.PHONY: clean
clean:
	$(MAKE) -C protocon clean

