/* SPDX-License-Identifier: BSD-2-Clause */

/**
 * @file
 *
 * @ingroup OceosTestCaseTaskMgr
 *
 * @brief Unity test case preamble for OCEOS Task Manager
 */

/*
 * Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
 */

/*
 * Unity test case preamble for OCEOS Task Manager
 * Template file for formal testing framework
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdbool.h>
#include "unity.h"
#include "oceos_internals.h"
#include "oceos_tasks_internal.h"

/**
 * @defgroup OceosTestCaseTaskMgr \
 *   OCEOS Task Manager Tests
 *
 * @ingroup OceosTestSuite
 *
 * @brief Unity tests for OCEOS task management operations
 *
 * This test case performs the following actions:
 *
 * - Run task management tests for OCEOS defined by formal model
 *
 * @{ 
 */

// Weak test hooks used by generated code
__attribute__((weak)) void OceosTest_SetTask(unsigned int task_id) {
    (void)task_id;
}

__attribute__((weak)) bool OceosTest_WaitForSuspend(unsigned int task_id, unsigned int timeout_ms) {
    (void)task_id; (void)timeout_ms;
    // Default: no wait, assume suspended immediately (override in OCEOS test harness)
    return true;
}

// Weak stubs for OCEOS APIs (override by linking real implementation)
__attribute__((weak)) enum DIRECTIVE_STATUS oceos_task_create(
    unsigned int        task_id,
    unsigned char       priority,
    unsigned char       threshold,
    unsigned char       jobs_max,
    bool                fp_used,
    bool                initially_enabled,
    void               (*start_function)(void *),
    void               (*end_function)(void *),
    unsigned int        time_deadline,
    unsigned int        time_mininterstart
) {
    (void)task_id; (void)priority; (void)threshold; (void)jobs_max; (void)fp_used; (void)initially_enabled;
    (void)start_function; (void)end_function; (void)time_deadline; (void)time_mininterstart;
    return (enum DIRECTIVE_STATUS)0;
}

__attribute__((weak)) enum DIRECTIVE_STATUS oceos_task_start(unsigned int task_id) {
    (void)task_id; return (enum DIRECTIVE_STATUS)0;
}

__attribute__((weak)) enum DIRECTIVE_STATUS oceos_task_delete(unsigned int task_id) {
    (void)task_id; return (enum DIRECTIVE_STATUS)0;
}

__attribute__((weak)) enum DIRECTIVE_STATUS oceos_task_suspend(unsigned int task_id) {
    (void)task_id; return (enum DIRECTIVE_STATUS)0;
}

__attribute__((weak)) enum DIRECTIVE_STATUS oceos_task_resume(unsigned int task_id) {
    (void)task_id; return (enum DIRECTIVE_STATUS)0;
}

__attribute__((weak)) enum DIRECTIVE_STATUS oceos_task_set_priority(unsigned int task_id, unsigned char new_priority, unsigned char *old_priority) {
    (void)task_id; (void)new_priority; if (old_priority) *old_priority = 0; return (enum DIRECTIVE_STATUS)0;
}

// OCEOS API function pointers for testing
static enum DIRECTIVE_STATUS TaskCreate(
    unsigned int        task_id,
    unsigned char       priority,
    unsigned char       threshold,
    unsigned char       jobs_max,
    bool               fp_used,
    bool               initially_enabled,
    void               (*start_function)(void *),
    void               (*end_function)(void *),
    unsigned int        time_deadline,
    unsigned int        time_mininterstart
)
{
    return oceos_task_create(
        task_id,
        priority,
        threshold,
        jobs_max,
        fp_used,
        initially_enabled,
        start_function,
        end_function,
        time_deadline,
        time_mininterstart
    );
}

static enum DIRECTIVE_STATUS TaskStart(
    unsigned int task_id
)
{
    return oceos_task_start(task_id);
}

static enum DIRECTIVE_STATUS TaskDelete(
    unsigned int task_id
)
{
    return oceos_task_delete(task_id);
}

static enum DIRECTIVE_STATUS TaskSuspend(
    unsigned int task_id
)
{
    return oceos_task_suspend(task_id);
}

static enum DIRECTIVE_STATUS TaskResume(
    unsigned int task_id
)
{
    return oceos_task_resume(task_id);
}

static enum DIRECTIVE_STATUS TaskSetPriority(
    unsigned int         task_id,
    unsigned char        new_priority,
    unsigned char       *old_priority
)
{
    return oceos_task_set_priority(task_id, new_priority, old_priority);
}

// Test context setup
void setUp(void)
{
    // default empty; override if needed
}

void tearDown(void)
{
    // default empty; override if needed
}
