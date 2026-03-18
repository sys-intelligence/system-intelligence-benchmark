CC           := gcc
CFLAGS       := $(shell pkg-config fuse --cflags) -pthread -Wall -O2 -I. -Iutil -Ifile -Iinode -Iinterface -Iinterface-util -Ipath
LDFLAGS      := $(shell pkg-config fuse --libs)

DEBUG_CFLAGS := -g -DDEBUG

TARGET       := atomfs-fuse
DEBUG_TARGET := $(TARGET)-debug

SOURCES      := $(shell find . -name '*.c')
OBJS         := $(SOURCES:.c=.o)
DEBUG_OBJS   := $(SOURCES:.c=-debug.o)

RM           := rm -f

.PHONY: all clean run debug

all: $(TARGET)

$(TARGET): $(OBJS)
	@echo "==> Linking Release: $@"
	$(CC) -o $@ $^ $(LDFLAGS)

$(DEBUG_TARGET): $(DEBUG_OBJS)
	@echo "==> Linking Debug:   $@"
	$(CC) -o $@ $^ $(LDFLAGS)

%.o: %.c
	@echo "Compiling (Release) $< -> $@"
	$(CC) $(CFLAGS) -c -o $@ $<

%-debug.o: %.c
	@echo "Compiling (Debug)   $< -> $@"
	$(CC) $(CFLAGS) $(DEBUG_CFLAGS) -c -o $@ $<

run: $(TARGET)
	@echo "==> Running filesystem..."
	-mkdir -p ~/atomfs > /dev/null 2>&1
	./$(TARGET) -n /dev/pmem0 ~/atomfs

debug: $(DEBUG_TARGET)
	@echo "==> Preparing to debug..."
	-mkdir -p /tmp/fs > /dev/null 2>&1
	-sudo umount /tmp/fs >/dev/null 2>&1
	echo "r -n /dev/pmem0 /tmp/fs" > /tmp/parms
	exec gdb -x /tmp/parms ./$(DEBUG_TARGET)

clean:
	@echo "==> Cleaning up project..."
	$(RM) $(TARGET) $(DEBUG_TARGET) $(OBJS) $(DEBUG_OBJS) /tmp/parms