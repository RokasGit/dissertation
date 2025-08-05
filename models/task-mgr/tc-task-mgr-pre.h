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

#include "unity.h"
#include "oceos_internals.h"
#include "oceos_tasks_internal.h"
#include "oceos-test-support.h"

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
    unity_setUp();
}

void tearDown(void)
{
    unity_tearDown();
}
