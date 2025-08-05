# OCEOS Unity Test Framework Makefile
# Build system for OCEOS formal testing with Unity framework
# Supports SPARC/LEON3 and ARM Cortex-M4 platforms
TEST_PATTERN ?= test_*.c
RUNNER_PATTERN ?= *_Runner.c

# Find test files - look for simple test files, not just runners
ALL_TEST_SRCS = $(wildcard $(TEST_DIR)/$(TEST_PATTERN))
RUNNER_SRCS = $(wildcard $(TEST_DIR)/$(RUNNER_PATTERN))
TEST_SRCS = $(filter-out $(RUNNER_SRCS),$(ALL_TEST_SRCS))

# If no runners exist, treat test files as standalone
ifeq ($(RUNNER_SRCS),)
    STANDALONE_TESTS = $(TEST_SRCS)
    TEST_EXES = $(patsubst $(TEST_DIR)/%.c,$(BIN_DIR)/%,$(STANDALONE_TESTS))
else
    # Object files
    RUNNER_OBJS = $(patsubst $(TEST_DIR)/%.c,$(OBJ_DIR)/%.o,$(RUNNER_SRCS))
    TEST_EXES = $(patsubst $(TEST_DIR)/%_Runner.c,$(BIN_DIR)/%,$(RUNNER_SRCS))
endif

# OCEOS Unity Test Framework Build System
# Cross-platform support for SPARC/LEON3 and ARM Cortex-M4

# Include SPARC tools configuration
include tools_config_sparc.mk

# Configuration
OCEOS_ROOT ?= C:/Users/rokas/OneDrive/Desktop/developer/dissertation/oceos
UNITY_ROOT ?= $(OCEOS_ROOT)/test/unity
FORMAL_TEST_ROOT ?= $(CURDIR)

# OCEOS BSP and target configuration
BSP ?= pm698
SPARC ?= 1
TOOLCHAIN ?= gcc
ARCHITECTURE ?= sparc
TARGET_CPU ?= leon3

# BCC2 SPARC Gaisler compiler setup
# Default to C:\opt\bcc-2.2.0-gcc on Windows
ifeq ($(OS),Windows_NT)
    BCC_ROOT ?= C:/opt/bcc-2.2.0-gcc
else
    BCC_ROOT ?= /opt/bcc-2.2.0-gcc
endif

# Determine toolchain prefix based on SPARC flag and BSP
ifeq ($(SPARC),1)
    CROSS_PREFIX = $(BCC_ROOT)/bin/sparc-gaisler-elf-
    ARCHITECTURE = sparc
else ifeq ($(ARCHITECTURE),arm)
    CROSS_PREFIX = arm-none-eabi-
else
    CROSS_PREFIX = 
endif

# Tools
CC = $(CROSS_PREFIX)$(TOOLCHAIN)
AR = $(CROSS_PREFIX)ar
AS = $(CROSS_PREFIX)as
LD = $(CROSS_PREFIX)ld
OBJCOPY = $(CROSS_PREFIX)objcopy
OBJDUMP = $(CROSS_PREFIX)objdump
SIZE = $(CROSS_PREFIX)size

# Directories - link to real OCEOS test structure
BUILD_DIR = build
OBJ_DIR ?= $(BUILD_DIR)/obj
BIN_DIR ?= $(BUILD_DIR)/bin
DEP_DIR ?= $(BUILD_DIR)/deps

SRC_DIR = src
TEST_DIR = $(OCEOS_ROOT)/test/common
COMMON_DIR = common
MODELS_DIR = models

# OCEOS test directories (use actual OCEOS tests)
OCEOS_TEST_DIRS = $(OCEOS_ROOT)/test/common/tasks1_test \
                  $(OCEOS_ROOT)/test/common/tasks2_test \
                  $(OCEOS_ROOT)/test/common/tasks3_test

# Include paths - use real OCEOS headers instead of stubs
INCLUDES = -I$(UNITY_ROOT)/src \
           -I$(OCEOS_ROOT)/include \
           -I$(OCEOS_ROOT)/src/include \
           -I$(OCEOS_ROOT)/src/$(ARCHITECTURE)/include \
           -I$(FORMAL_TEST_ROOT)/$(COMMON_DIR) \
           -I$(FORMAL_TEST_ROOT)/$(SRC_DIR) \
           -I.

# Compiler flags
CFLAGS = -Wall -Wextra -std=c99 -g3 -O0
CFLAGS += $(INCLUDES)
CFLAGS += -DUNITY_INCLUDE_CONFIG_H
CFLAGS += -DOCEOS_FORMAL_TESTING

# Architecture-specific flags for BCC2 SPARC
ifeq ($(SPARC),1)
    CFLAGS += -mcpu=$(TARGET_CPU) -msoft-float
    CFLAGS += -DTARGET_SPARC -DTARGET_LEON3 -DBSP_$(BSP)
    LDFLAGS += -mcpu=$(TARGET_CPU) -msoft-float
    # BCC2 specific flags
    CFLAGS += -DBCC2_SPARC -DGAISLER_LEON3
else ifeq ($(ARCHITECTURE),arm)
    CFLAGS += -mcpu=cortex-m4 -mthumb -mfloat-abi=soft
    CFLAGS += -DTARGET_ARM -DTARGET_CORTEX_M4
    LDFLAGS += -mcpu=cortex-m4 -mthumb -mfloat-abi=soft
endif

# Debug/Release configuration
DEBUG ?= 1
ifeq ($(DEBUG),1)
    CFLAGS += -DDEBUG -g3
else
    CFLAGS += -DNDEBUG -O2
endif

# Coverage support
COVERAGE ?= 0
ifeq ($(COVERAGE),1)
    CFLAGS += -fprofile-arcs -ftest-coverage
    LDFLAGS += -lgcov --coverage
endif

# Source files - include real OCEOS components
UNITY_SRCS = $(UNITY_ROOT)/src/unity.c
COMMON_SRCS = $(wildcard $(COMMON_DIR)/*.c)
SUPPORT_SRCS = $(wildcard $(SRC_DIR)/*.c)

# OCEOS object files (precompiled from OCEOS source)
OCEOS_OBJS = $(wildcard $(COMMON_DIR)/*.o)

# Test source patterns - find real OCEOS tests
TEST_PATTERN ?= *_test.c
TEST_RUNNER_PATTERN ?= *_Runner.c

# Find test files from OCEOS test directories
TEST_SRCS = $(foreach dir,$(OCEOS_TEST_DIRS),$(wildcard $(dir)/*_test.c))
RUNNER_SRCS = $(foreach dir,$(OCEOS_TEST_DIRS),$(wildcard $(dir)/*_Runner.c))
OCEOS_OBJ_FILES = $(foreach dir,$(OCEOS_TEST_DIRS),$(wildcard $(dir)/*.o))

# Object files - handle OCEOS test structure
UNITY_OBJS = $(patsubst $(UNITY_ROOT)/src/%.c,$(OBJ_DIR)/%.o,$(UNITY_SRCS))
COMMON_OBJS = $(patsubst $(COMMON_DIR)/%.c,$(OBJ_DIR)/%.o,$(COMMON_SRCS))
SUPPORT_OBJS = $(patsubst $(SRC_DIR)/%.c,$(OBJ_DIR)/%.o,$(SUPPORT_SRCS))

# OCEOS test objects - create object files in our build directory from OCEOS test sources
TEST_OBJS = $(patsubst %.c,$(OBJ_DIR)/%.o,$(notdir $(TEST_SRCS)))
RUNNER_OBJS = $(patsubst %.c,$(OBJ_DIR)/%.o,$(notdir $(RUNNER_SRCS)))

# Test executables - based on runner files
TEST_EXES = $(patsubst %_Runner.c,$(BIN_DIR)/%,$(notdir $(RUNNER_SRCS)))

# OCEOS library (if needed)
OCEOS_LIB ?= $(OCEOS_ROOT)/lib/liboceos.a

# OCEOS-specific build targets (following OCEOS test patterns)
.PHONY: test_build_only oceos_test formal_verify build_oceos_tests

# Build OCEOS tests using their native build system
build_oceos_tests:
	@echo "Building OCEOS tests using native build system..."
	@cd "$(OCEOS_ROOT)/test/common/tasks1_test" && make tasks1_build_test BSP=$(BSP) SPARC=$(SPARC) TOOLCHAIN=$(TOOLCHAIN)
	@cd "$(OCEOS_ROOT)/test/common/tasks2_test" && make tasks2_build_test BSP=$(BSP) SPARC=$(SPARC) TOOLCHAIN=$(TOOLCHAIN)
	@cd "$(OCEOS_ROOT)/test/common/tasks3_test" && make tasks3_build_test BSP=$(BSP) SPARC=$(SPARC) TOOLCHAIN=$(TOOLCHAIN)

# Build only (matches OCEOS test command pattern) - use OCEOS native builds
test_build_only: setup build_oceos_tests
	@echo "Build completed for BSP=$(BSP) SPARC=$(SPARC) TOOLCHAIN=$(TOOLCHAIN)"
	@echo "OCEOS tests built using native build system"

# OCEOS test execution
ifeq ($(OS),Windows_NT)
# Windows: run the OCEOS-built test executables directly
oceos_test: test_build_only
	@echo "Running OCEOS Unity tests..."
	@echo Executing tasks_test.exe...
	@pushd "$(OCEOS_ROOT)\test\common\tasks1_test\build" >NUL & tasks_test.exe & popd >NUL
	@echo Executing tasks2_test.exe...
	@pushd "$(OCEOS_ROOT)\test\common\tasks2_test\build" >NUL & tasks2_test.exe & popd >NUL
	@echo Executing tasks3_test.exe...
	@pushd "$(OCEOS_ROOT)\test\common\tasks3_test\build" >NUL & tasks3_test.exe & popd >NUL

# Also adapt generic test target to Windows
test: $(TEST_EXES)
	@echo "Running Unity tests..."
	@for %%F in ($(subst /,\,$(TEST_EXES))) do (
		echo Running %%F... & call %%F || echo Test %%F failed
	)
else
# Unix-like: keep POSIX shell loops
oceos_test: test_build_only
	@echo "Running OCEOS tests..."
	@"$(OCEOS_ROOT)/test/common/tasks1_test/build/tasks_test.exe" || true
	@"$(OCEOS_ROOT)/test/common/tasks2_test/build/tasks2_test.exe" || true
	@"$(OCEOS_ROOT)/test/common/tasks3_test/build/tasks3_test.exe" || true

test: $(TEST_EXES)
	@echo "Running Unity tests..."
	@for test in $(TEST_EXES); do \
		echo "Running $$test..."; \
		"$$test" || echo "Test $$test failed"; \
	done
endif

# Build with OCEOS command pattern
build: test_build_only

help:
	@echo "OCEOS Unity Test Framework"
	@echo ""
	@echo "Targets:"
	@echo "  test_build_only - Build tests only (matches OCEOS pattern)"
	@echo "  oceos_test      - Build and run all tests"
	@echo "  clean           - Clean build artifacts"
	@echo "  formal-test     - Run formal test generation"
	@echo "  models          - Generate tests from Promela models"
	@echo "  verify-bcc2     - Verify BCC2 SPARC compiler installation"
	@echo "  setup           - Create build directories"
	@echo ""
	@echo "OCEOS Configuration:"
	@echo "  BSP=$(BSP) (pm698, gr712rc, leon3)"
	@echo "  SPARC=$(SPARC) (1 for SPARC, 0 for other)"
	@echo "  TOOLCHAIN=$(TOOLCHAIN) (gcc)"
	@echo "  ARCHITECTURE=$(ARCHITECTURE)"
	@echo "  DEBUG=$(DEBUG)"
	@echo "  COVERAGE=$(COVERAGE)"
	@echo ""
	@echo "Example OCEOS build command:"
	@echo "  make test_build_only BSP=pm698 SPARC=1 TOOLCHAIN=gcc"

# Windows-specific adjustments
ifeq ($(OS),Windows_NT)
    # Use Windows shell commands
    MKDIR_P = if not exist "$(dir $@)" mkdir "$(dir $@)"
    RM_RF = if exist "$1" rmdir /s /q "$1"
    SHELL = cmd.exe
else
    # Unix-like systems
    MKDIR_P = mkdir -p $(dir $@)
    RM_RF = rm -rf $1
endif

setup:
ifeq ($(OS),Windows_NT)
	@if not exist "$(subst /,\,$(BUILD_DIR))" mkdir "$(subst /,\,$(BUILD_DIR))"
	@if not exist "$(subst /,\,$(OBJ_DIR))" mkdir "$(subst /,\,$(OBJ_DIR))"
	@if not exist "$(subst /,\,$(BIN_DIR))" mkdir "$(subst /,\,$(BIN_DIR))"
	@if not exist "$(subst /,\,$(DEP_DIR))" mkdir "$(subst /,\,$(DEP_DIR))"
else
	@mkdir -p $(BUILD_DIR) $(OBJ_DIR) $(BIN_DIR) $(DEP_DIR)
endif

# Build Unity library objects
$(OBJ_DIR)/%.o: $(UNITY_ROOT)/src/%.c
	@echo "Compiling Unity: $<"
	@$(CC) $(CFLAGS) -c $< -o $@

# Build common objects
$(OBJ_DIR)/%.o: $(COMMON_DIR)/%.c
	@echo "Compiling Common: $<"
	@$(CC) $(CFLAGS) -c $< -o $@

# Build support objects
$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c
	@echo "Compiling Support: $<"
	@$(CC) $(CFLAGS) -c $< -o $@

# Build test objects from OCEOS test directories
$(OBJ_DIR)/%.o: $(OCEOS_ROOT)/test/common/tasks1_test/%.c
	@echo "Compiling OCEOS Test: $<"
	@$(CC) $(CFLAGS) -c $< -o $@

$(OBJ_DIR)/%.o: $(OCEOS_ROOT)/test/common/tasks2_test/%.c
	@echo "Compiling OCEOS Test: $<"
	@$(CC) $(CFLAGS) -c $< -o $@

$(OBJ_DIR)/%.o: $(OCEOS_ROOT)/test/common/tasks3_test/%.c
	@echo "Compiling OCEOS Test: $<"
	@$(CC) $(CFLAGS) -c $< -o $@

# Build test objects - fallback rule
$(OBJ_DIR)/%.o: $(TEST_DIR)/%.c
	@echo "Compiling Test: $<"
	@$(CC) $(CFLAGS) -c $< -o $@

# Link test executables (with runners) - include OCEOS objects
$(BIN_DIR)/%: $(OBJ_DIR)/%_Runner.o $(UNITY_OBJS) $(COMMON_OBJS) $(SUPPORT_OBJS) $(OCEOS_OBJ_FILES)
	@echo "Linking: $@"
	@$(CC) $(LDFLAGS) $^ -o $@
	@$(SIZE) $@

# Link standalone test executables (without runners) - include OCEOS objects  
$(BIN_DIR)/%: $(OBJ_DIR)/%.o $(UNITY_OBJS) $(COMMON_OBJS) $(SUPPORT_OBJS) $(OCEOS_OBJ_FILES)
	@echo "Linking standalone test: $@"
	@$(CC) $(LDFLAGS) $^ -o $@
	@$(SIZE) $@

# Formal test generation from Promela models
formal-test:
	@echo "Generating formal tests from Promela models..."
ifeq ($(OS),Windows_NT)
	@cmd /c "env\Scripts\activate && python testbuilder_oceos.py allsteps allmodels"
else
	@source env/bin/activate && python testbuilder_oceos.py allsteps allmodels
endif

# Generate tests for specific model
models/%:
	@echo "Generating tests for model: $*"
	@python3 testbuilder_oceos.py allsteps $*

# Model-specific targets
task-mgr: models/task-mgr
event-mgr: models/event-mgr
sem-mgr: models/sem-mgr

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
ifeq ($(OS),Windows_NT)
	@if exist "$(BUILD_DIR)" rmdir /s /q "$(BUILD_DIR)"
	@if exist "*.gcov" del /q *.gcov
	@if exist "*.gcda" del /q *.gcda  
	@if exist "*.gcno" del /q *.gcno
else
	@rm -rf $(BUILD_DIR)
	@find . -name "*.gcov" -delete
	@find . -name "*.gcda" -delete
	@find . -name "*.gcno" -delete
endif

# Generate coverage report (if coverage enabled)
coverage: test
ifeq ($(COVERAGE),1)
	@echo "Generating coverage report..."
	@gcov $(TEST_OBJS) $(COMMON_OBJS) $(SUPPORT_OBJS)
	@lcov --capture --directory . --output-file coverage.info
	@genhtml coverage.info --output-directory coverage_html
	@echo "Coverage report generated in coverage_html/"
endif

# Install dependencies (placeholder)
install-deps:
	@echo "Installing dependencies..."
	@echo "Please ensure Unity framework is available at $(UNITY_ROOT)"
	@echo "Please ensure OCEOS source is available at $(OCEOS_ROOT)"

# Dependency generation
$(DEP_DIR)/%.d: $(TEST_DIR)/%.c
	@$(CC) $(CFLAGS) -MM -MT $(OBJ_DIR)/$*.o $< > $@

$(DEP_DIR)/%.d: $(COMMON_DIR)/%.c
	@$(CC) $(CFLAGS) -MM -MT $(OBJ_DIR)/$*.o $< > $@

$(DEP_DIR)/%.d: $(SRC_DIR)/%.c
	@$(CC) $(CFLAGS) -MM -MT $(OBJ_DIR)/$*.o $< > $@

# Include dependencies if they exist
# Only include dependency files when the dependency directory exists to avoid
# spurious errors (e.g., when running `make setup` before directories exist)
ifneq ($(wildcard $(DEP_DIR)),)
-include $(TEST_SRCS:$(TEST_DIR)/%.c=$(DEP_DIR)/%.d)
-include $(COMMON_SRCS:$(COMMON_DIR)/%.c=$(DEP_DIR)/%.d)
-include $(SUPPORT_SRCS:$(SRC_DIR)/%.c=$(DEP_DIR)/%.d)
endif

# SPIN model checking (requires SPIN to be installed)
verify-model:
	@echo "Verifying Promela models with SPIN..."
	@for model in $(wildcard $(MODELS_DIR)/*/*.pml); do \
		echo "Verifying $$model..."; \
		spin -a $$model && \
		gcc -o pan pan.c && \
		./pan || echo "Verification failed for $$model"; \
		rm -f pan pan.c; \
	done

# Generate HTML documentation
docs:
	@echo "Generating documentation..."
	@doxygen Doxyfile 2>/dev/null || echo "Doxygen not available"

# Print configuration
config:
	@echo "Build Configuration:"
	@echo "  BSP: $(BSP)"
	@echo "  TOOLCHAIN: $(TOOLCHAIN)"  
	@echo "  ARCHITECTURE: $(ARCHITECTURE)"
	@echo "  CROSS_PREFIX: $(CROSS_PREFIX)"
	@echo "  CC: $(CC)"
	@echo "  CFLAGS: $(CFLAGS)"
	@echo "  LDFLAGS: $(LDFLAGS)"
	@echo "  OCEOS_ROOT: $(OCEOS_ROOT)"
	@echo "  UNITY_ROOT: $(UNITY_ROOT)"
	@echo "  DEBUG: $(DEBUG)"
	@echo "  COVERAGE: $(COVERAGE)"
