
CC = gcc
CFLAGS =
CFLAGS += -g
#CFLAGS += -O3
CFLAGS += -ansi -pedantic
CFLAGS += -Wall -Wextra -Wstrict-aliasing

cx_path = ../cx
bin_path = ../bin

IFLAGS = -I..

CFLAGS += $(IFLAGS)

exe_list = satsyn
exe_list := $(addprefix $(bin_path)/,$(exe_list))

all: $(exe_list)

cx_obj_list = fileb.o syscx.o bstree.o rbtree.o ospc.o
cx_obj_list := $(addprefix $(cx_path)/,$(cx_obj_list))

$(bin_path)/satsyn: satsyn.o $(cx_obj_list)
	$(CC) $(CFLAGS) -o $@ satsyn.o $(cx_obj_list)

%.o: %.c
	$(CC) -c $(CFLAGS) $< -o $@

satsyn.o: dimacs.c pla.c promela.c \
	inst-sat3.c inst-matching.c inst-coloring.c inst-bit3.c

$(exe_list): | $(bin_path)

$(bin_path):
	mkdir -p $(bin_path)

.PHONY: clean
clean:
	rm -f *.o $(exe_list) $(cx_path)/*.o

