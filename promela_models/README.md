# OCEOS Promela Models Project

This project contains Promela models for formal verification of the OCEOS Real-Time Operating System components, specifically focusing on task management operations.

## Project Structure

```
promela_models/
├── README.md                    # This file
├── Makefile                     # Build automation and verification
├── task_management/             # Core task management models
│   ├── create_task.pml         # CreateTask operation model
│   └── task_states.pml         # Task state management
└── verification_scripts/        # Verification and property checking
    ├── properties.pml          # LTL properties and assertions
    └── model_checker_config.txt # SPIN configuration

```

## Overview

This project implements formal verification models for OCEOS task management using Promela/SPIN model checker. The models capture:

- Task creation and initialization processes
- Task state transitions
- Priority-based scheduling behavior
- Resource allocation and deallocation
- Error conditions and exception handling

## Getting Started

### Prerequisites
- SPIN model checker installed on your system
- GCC compiler for generating verification executables
- Make utility for build automation

### Basic Usage

1. **Syntax Check**: Verify model syntax
   ```bash
   make syntax-check
   ```

2. **Run Full Verification**: Verify all models and properties
   ```bash
   make verify-all
   ```

3. **Generate Coverage Report**: Analyze code coverage
   ```bash
   make coverage
   ```

4. **Generate Statistics**: Get performance statistics
   ```bash
   make statistics
   ```

5. **Clean Build Artifacts**: Remove generated files
   ```bash
   make clean
   ```

### Verification Output
- Results are saved to the `results/` directory (auto-created)
- Verification logs contain detailed analysis of properties
- Coverage reports show model execution paths

## Model Methodology

The models follow the formal verification methodology described in the dissertation documentation:

1. **Abstract System Modeling**: Core OCEOS operations modeled as Promela processes
2. **Property Specification**: Safety and liveness properties defined in LTL
3. **Automated Verification**: Exhaustive state space exploration using SPIN via Makefile
4. **Analysis & Reporting**: Comprehensive coverage and statistical analysis

## Key Features

- **Accurate Task Modeling**: Reflects OCEOS task descriptor structure and behavior
- **Comprehensive Verification**: Automated verification through Makefile targets
- **LTL Property Checking**: Formal verification of safety and liveness properties
- **Error Modeling**: Comprehensive error condition coverage
- **Build Automation**: Complete build and verification pipeline via Makefile
- **Configurable Analysis**: Multiple verification modes (safety, coverage, statistics)

## Available Make Targets

- `make all` - Run complete verification and generate tests
- `make syntax-check` - Check syntax of all models
- `make verify-all` - Verify all models with safety checks
- `make verify-create-task` - Verify CreateTask model specifically
- `make verify-task-states` - Verify TaskStates model specifically
- `make verify-properties` - Verify LTL properties individually
- `make simulate` - Run random simulations
- `make coverage` - Generate coverage analysis
- `make statistics` - Generate performance statistics
- `make clean` - Clean all generated files
