# Makefile for Raft Trace Generator using RedisRaft Core Library

CC = gcc
CFLAGS = -Wall -Wextra -std=c99 -O2 -g
LDFLAGS = -lpthread

# Paths
REDISRAFT_DIR = ../../../../data/repositories/redisraft
RAFT_INCLUDE_DIR = $(REDISRAFT_DIR)/deps/raft/include
RAFT_LIB_DIR = $(REDISRAFT_DIR)/deps/raft/build

# Source files
SOURCES = raft_trace_generator.c
TARGET = raft_trace_generator

# Include directories
INCLUDES = -I$(RAFT_INCLUDE_DIR)

# Libraries - use static lib directly for reliability
RAFT_STATIC_LIB = $(RAFT_LIB_DIR)/libraft.a

# Default target
all: build_raft $(TARGET)

# Build the Raft library first
build_raft:
	@echo "Building Raft library..."
	@cd $(REDISRAFT_DIR)/deps/raft && \
	if [ ! -d build ]; then mkdir build; fi && \
	cd build && \
	cmake .. -DCMAKE_BUILD_TYPE=Release && \
	make

# Build the trace generator
$(TARGET): $(SOURCES)
	@echo "Building Raft trace generator..."
	$(CC) $(CFLAGS) $(INCLUDES) -o $(TARGET) $(SOURCES) $(RAFT_STATIC_LIB) $(LDFLAGS)

# Test target
test: $(TARGET)
	@echo "Running Raft trace generator test..."
	./$(TARGET) 3 15 /tmp/raft_test_traces

# Clean build artifacts
clean:
	rm -f $(TARGET)
	rm -rf /tmp/raft_test_traces

# Clean everything including Raft library
clean-all: clean
	rm -rf $(RAFT_LIB_DIR)

# Install dependencies (if needed)
deps:
	@echo "Installing build dependencies..."
	sudo apt-get update
	sudo apt-get install -y build-essential cmake

# Print configuration
info:
	@echo "Configuration:"
	@echo "  CC: $(CC)"
	@echo "  CFLAGS: $(CFLAGS)"
	@echo "  RAFT_INCLUDE_DIR: $(RAFT_INCLUDE_DIR)"
	@echo "  RAFT_LIB_DIR: $(RAFT_LIB_DIR)"
	@echo "  SOURCES: $(SOURCES)"
	@echo "  TARGET: $(TARGET)"

.PHONY: all build_raft test clean clean-all deps info