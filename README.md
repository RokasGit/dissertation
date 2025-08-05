# OCEOS Formal Testing Framework

Formal testing framework for OCEOS (On-board Computing Embedded Operating System) using SPIN model checking and Unity test framework for automated test generation and execution.

## Overview

This framework provides formal verification capabilities for OCEOS components:

- **Model-Based Testing**: Promela models specify OCEOS behavior
- **Test Generation**: SPIN traces converted to Unity test code
- **OCEOS Integration**: Native OCEOS API integration
- **Multi-Target Support**: SPARC/LEON3 and ARM Cortex-M4 platforms
- **Unity Framework**: Professional test execution and reporting

## Architecture

### Core Components

1. **testbuilder_oceos.py** - Main test generation script (adapted from RTEMS testbuilder.py)
2. **spin2test_oceos.py** - Converts SPIN traces to Unity test code
3. **refine-config-oceos.yml** - Maps Promela constructs to OCEOS Unity code
4. **Unity Test Support** - Helper functions for OCEOS Unity testing
5. **Promela Models** - Formal models of OCEOS components

### Directory Structure

```
Project/
├── src/                          # Core framework source
│   └── spin2test_oceos/         # SPIN to Unity converter
├── models/                       # Promela models
│   ├── task-mgr/                # Task management model
│   ├── sem-mgr/                 # Semaphore management model
│   └── models.yml               # Model registry
├── common/                       # Common support files
│   ├── oceos.pml                # OCEOS Promela definitions
│   ├── oceos-test-support.h     # Unity test support
│   └── oceos-test-support.c
├── tests/                        # Generated and manual tests
│   └── unity/                   # Unity test files
├── build/                        # Build artifacts
├── Makefile                      # Build system
└── setup_oceos.sh               # Setup script
```

## Getting Started

### Prerequisites

1. **SPIN Model Checker** - Download from http://spinroot.com/
2. **Unity Test Framework** - Clone from https://github.com/ThrowTheSwitch/Unity.git
3. **Python 3.7+** with PyYAML
4. **BCC2 SPARC Gaisler Compilers**:
   - Download `bcc-2.2.0-gcc-mingw64.zip` from https://download.gaisler.com/anonftp/bcc2/bin/
   - Create `C:\opt` directory on Windows (or `/opt` on Linux)
   - Extract BCC2 to `C:\opt\bcc-2.2.0-gcc` 
   - For non-Windows systems, modify `tools_config_sparc.mk` with correct paths
   - **Note**: BCC2 is only available for Linux and Windows (not macOS)
5. **GNU Make** - Ensure `make` is installed on your system
6. **OCEOS Source Code**

### Setup

1. **Clone and setup the framework**:
   ```bash
   git clone <repository-url> oceos-formal-testing
   cd oceos-formal-testing
   chmod +x setup_oceos.sh
   ./setup_oceos.sh
   ```

2. **Activate Python environment**:
   ```bash
   source env/bin/activate
   ```

3. **Configure paths** in `testbuilder_oceos.yml`:
   ```yaml
   oceos: /path/to/oceos/source
   unity_framework: /path/to/unity/src
   test_runner: /path/to/test/runner
   ```

4. **Verify setup**:
   ```bash
   make config
   make help
   ```

## Usage

### Basic Commands

1. **Build tests only (following OCEOS pattern)**:
   ```bash
   make test_build_only BSP=pm698 SPARC=1 TOOLCHAIN=gcc
   ```

2. **Build and run tests**:
   ```bash
   make oceos_test BSP=pm698 SPARC=1 TOOLCHAIN=gcc
   ```

3. **Verify BCC2 compiler installation**:
   ```bash
   make verify-bcc2
   ```

4. **Generate formal tests from all models**:
   ```bash
   python3 testbuilder_oceos.py allsteps allmodels
   ```

5. **Generate tests for specific model**:
   ```bash
   python3 testbuilder_oceos.py allsteps task-mgr
   ```

### Manual Test Generation

1. **Generate SPIN trails for a model**:
   ```bash
   python3 testbuilder_oceos.py spin task-mgr
   ```

2. **Generate Unity tests from trails**:
   ```bash
   python3 testbuilder_oceos.py gentests task-mgr
   ```

3. **Copy tests to OCEOS test directory**:
   ```bash
   python3 testbuilder_oceos.py copy task-mgr
   ```

4. **Full pipeline for one model**:
   ```bash
   python3 testbuilder_oceos.py allsteps task-mgr
   ```

### Adding New Models

1. **Create model directory**:
   ```bash
   mkdir models/my-component
   ```

2. **Write Promela model** (`models/my-component/my-component-model.pml`):
   ```promela
   #include "../common/oceos.pml"
   // Your model here
   ```

3. **Create refinement file** (`models/my-component/my-component-rfn.yml`):
   ```yaml
   LANGUAGE: C
   # Your refinements here
   ```

4. **Register model** in `models/models.yml`:
   ```yaml
   my-component: my-component/my-component-model
   ```

5. **Generate tests**:
   ```bash
   make models/my-component
   ```

## Writing OCEOS Promela Models

### Basic Structure

```promela
/* Include OCEOS definitions */
#include "../common/oceos.pml"

/* Model-specific constants */
#define COMPONENT_MAX 5

/* Global variables */
byte createRC;
byte deleteRC;
bool testScenario;

/* Scenario selection */
inline chooseScenario() {
    if
    :: scenario = CreateDelete;
    :: scenario = ErrorHandling;
    fi
}

/* Main processes */
proctype TestRunner() {
    /* Test logic here */
    printf("@@@ %d CALL oceos_component_create %d createRC\n", _pid, component_id);
    oceos_component_create(component_id, createRC);
    printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);
}

init {
    chooseScenario();
    run TestRunner();
    _nr_pr == 1;
    #ifdef TEST_GEN
    assert(false);
    #endif
}
```

### Key Annotations

- **CALL**: Marks OCEOS API calls
- **SCALAR**: Marks return values for assertions
- **LOG**: Marks scenario descriptions
- **ASSERT**: Marks conditions to verify

## Unity Test Integration

### Test Structure

Generated Unity tests follow this pattern:

```c
#include "unity.h"
#include "oceos-test-support.h"

void setUp(void) {
    unity_setUp();
}

void tearDown(void) {
    unity_tearDown();
}

void test_oceos_component_scenario_0(void) {
    enum DIRECTIVE_STATUS result;
    unsigned int component_id = 1;
    
    // Generated from SPIN trace
    result = oceos_component_create(component_id, /* params */);
    TEST_ASSERT_EQUAL(SUCCESSFUL, result);
    
    result = oceos_component_delete(component_id);
    TEST_ASSERT_EQUAL(SUCCESSFUL, result);
}

int main(void) {
    UNITY_BEGIN();
    RUN_TEST(test_oceos_component_scenario_0);
    return UNITY_END();
}
```

### Custom Assertions

The framework provides OCEOS-specific assertions:

```c
TEST_ASSERT_OCEOS_SUCCESS(result);
TEST_ASSERT_OCEOS_ERROR(INVALID_ID, result);
TEST_ASSERT_TASK_STATE(task_id, Ready);
```

## Target Platforms

### SPARC/LEON3

```bash
make BSP=sparc-leon3 TOOLCHAIN=gcc ARCHITECTURE=sparc
```

### ARM Cortex-M4

```bash
make BSP=arm-cortex-m4 TOOLCHAIN=gcc ARCHITECTURE=arm
```

## Configuration Files

### testbuilder_oceos.yml

Main configuration file for the test generation framework:

```yaml
# Paths
spin2test: /path/to/spin2test_oceos.py
modelsfile: /path/to/models/models.yml
oceos: /path/to/oceos/source
unity_framework: /path/to/unity/src

# Test configuration
testsuite: oceos-model-0
target_platform: sparc-leon3
build_system: make
enable_coverage: true
```

### refine-config-oceos.yml

Maps Promela constructs to OCEOS Unity code:

```yaml
LANGUAGE: C

# Variable declarations
task_id_DCL: unsigned int {0}[OCEOS_TASK_MAX];
result_DCL: enum DIRECTIVE_STATUS

# API mappings
oceos_task_create: |
  {5} = oceos_task_create({0}, {1}, {2}, {3}, {4}, TRUE, 
                          test_task_function, test_task_end, 1000, 500);

# Assertions
createRC: |
  TEST_ASSERT_EQUAL_MESSAGE({0}, createRC, "Task creation return code");
```

## Debugging and Troubleshooting

### Common Issues

1. **SPIN not found**: Install SPIN model checker
2. **Unity not found**: Clone Unity framework
3. **Toolchain errors**: Install correct cross-compiler
4. **Python import errors**: Activate virtual environment

### Debug Mode

```bash
make DEBUG=1 all
```

### Verbose Output

```bash
python3 testbuilder_oceos.py --verbose allsteps task-mgr
```

### Coverage Analysis

```bash
make COVERAGE=1 test coverage
```

## Contributing

1. **Follow existing patterns** for new models and refinements
2. **Test thoroughly** with multiple scenarios
3. **Document new APIs** in refinement files
4. **Maintain compatibility** with Unity framework

## Examples

### Task Management Example

The task management model (`models/task-mgr/`) demonstrates:
- Task creation with various parameters
- Task lifecycle management
- Error condition testing
- Priority inheritance testing

### Generated Unity Test

From the task management model, the framework generates tests like:

```c
void test_TaskMgr_CreateDelete_Scenario_0(void) {
    enum DIRECTIVE_STATUS result;
    unsigned int task_id = 1;
    
    // Create task
    result = oceos_task_create(task_id, 10, 10, 5, FALSE, TRUE,
                              test_task_function, test_task_end, 1000, 500);
    TEST_ASSERT_EQUAL_MESSAGE(SUCCESSFUL, result, "Task creation should succeed");
    
    // Delete task
    result = oceos_task_delete(task_id);
    TEST_ASSERT_EQUAL_MESSAGE(SUCCESSFUL, result, "Task deletion should succeed");
}
```

## References

- [RTEMS Formal Testing Framework](https://devel.rtems.org/wiki/Formal)
- [SPIN Model Checker](http://spinroot.com/)
- [Unity Test Framework](http://www.throwtheswitch.org/unity)
- [OCEOS Documentation](link-to-oceos-docs)

## License

SPDX-License-Identifier: BSD-2-Clause

Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
Adapted for OCEOS with Unity testing framework
