/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * model.pml
 *
 * Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
 * Adapted for OCEOS
 *
 * Common Model Definitions for OCEOS Promela Models
 * Shared constants, structures, and utilities
 */

/* Model execution control */
#define MAX_ITERATIONS 10
#define TEST_TIMEOUT   100

/* Test scenario control */
bool scenario_complete = false;
bool test_passed = false;
byte current_scenario = 0;

/* Global test state */
byte test_step = 0;
byte error_count = 0;

/* Assertion and logging support */
#define test_assert(condition, message) \
    if \
    :: (condition) -> \
        skip; \
    :: else -> \
        printf("@@@ ASSERTION FAILED: %s\n", message); \
        assert(false); \
    fi

#define test_log(message) \
    printf("@@@ %d LOG: %s\n", _pid, message)

#define test_step_begin(step_name) \
    printf("@@@ %d STEP BEGIN: %s\n", _pid, step_name)

#define test_step_end(step_name) \
    printf("@@@ %d STEP END: %s\n", _pid, step_name)

/* Scenario control macros */
#define BEGIN_SCENARIO(name) \
    test_step_begin(name); \
    scenario_complete = false;

#define END_SCENARIO(name) \
    scenario_complete = true; \
    test_step_end(name);

/* Common test patterns */
#define wait_for_condition(condition, timeout) \
    byte wait_count = 0; \
    do \
    :: (condition) -> break; \
    :: (wait_count >= timeout) -> \
        printf("@@@ TIMEOUT waiting for condition\n"); \
        break; \
    :: else -> \
        wait_count++; \
    od

/* Memory barrier for atomic operations */
#define memory_barrier() atomic { skip; }

/* Test result reporting */
#define report_test_result(passed, test_name) \
    if \
    :: (passed) -> \
        printf("@@@ TEST PASSED: %s\n", test_name); \
    :: else -> \
        printf("@@@ TEST FAILED: %s\n", test_name); \
    fi
