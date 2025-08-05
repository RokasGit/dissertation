/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * task-mgr-h.pml
 *
 * Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
 *
 * OCEOS Task Manager Header Definitions
 * Task structures and constants for Promela modeling
 */

// Task state constants compatible with OCEOS
#define Ready      TASK_READY
#define Running    TASK_RUNNING  
#define Waiting    TASK_WAITING
#define Suspended  TASK_SUSPENDED
#define Terminated TASK_TERMINATED
#define Zombie     TASK_TERMINATED  // Zombie is same as terminated in OCEOS
#define Dormant    TASK_DORMANT

// Additional task states for modeling
#define Invalid    99

// Task structure definition using arrays (Promela compatible)
// Instead of struct, use parallel arrays for task properties
byte task_nodeid[TASK_MAX];
byte task_pmlid[TASK_MAX];
byte task_state[TASK_MAX];
byte task_priority[TASK_MAX];
byte task_threshold[TASK_MAX];
byte task_ids[TASK_MAX];  // Renamed to avoid conflict with parameters
bool task_enabled[TASK_MAX];
bool task_suspended[TASK_MAX];
bool task_created[TASK_MAX];
bool task_started[TASK_MAX];
bool task_terminated[TASK_MAX];

// Global task array - use typedef for compatibility
typedef TaskControlBlock {
    byte nodeid;
    byte pmlid;
    byte state;
};

// Simple task array for basic compatibility
TaskControlBlock tasks[TASK_MAX];

// Global semaphore array for synchronization
byte semaphores[SEM_MAX];

// Task ID constants for common tasks
#define RUNNER_TASK_ID 0
#define TASK_0_ID      1
#define TASK_1_ID      2
#define INVALID_TASK_ID 255

// Initialize task control blocks
inline initTasks() {
    byte i;
    for (i : 0 .. (TASK_MAX-1)) {
        tasks[i].nodeid = 0;
        tasks[i].pmlid = 0;
        tasks[i].state = Dormant;
        task_priority[i] = 0;
        task_threshold[i] = 0;
        task_id[i] = 0;
        task_enabled[i] = false;
        task_suspended[i] = false;
        task_created[i] = false;
        task_started[i] = false;
        task_terminated[i] = false;
    }
}

// Initialize semaphores
inline initSemaphores() {
    byte i;
    for (i : 0 .. (SEM_MAX-1)) {
        semaphores[i] = 0;
    }
}

// Helper macros for task state checking
#define isTaskReady(tid)      (tasks[tid].state == Ready)
#define isTaskRunning(tid)    (tasks[tid].state == Running)
#define isTaskSuspended(tid)  (tasks[tid].state == Suspended)
#define isTaskTerminated(tid) (tasks[tid].state == Terminated || tasks[tid].state == Zombie)
#define isTaskCreated(tid)    (task_created[tid] == true)
#define isTaskStarted(tid)    (task_started[tid] == true)

// Helper macros for valid IDs
#define isValidTaskId(tid)    (tid > 0 && tid < TASK_MAX)
#define isInvalidTaskId(tid)  (tid == 0 || tid >= TASK_MAX)

// Priority constants for testing
#define TEST_PRIO_LOW    1
#define TEST_PRIO_MED    10
#define TEST_PRIO_HIGH   20
#define TEST_PRIO_MAX    255
