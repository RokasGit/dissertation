/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * oceos.pml
 *
 * Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
 * Adapted for OCEOS
 *
 * Common OCEOS definitions for Promela models
 */

// OCEOS Task Management Constants
#define OCEOS_TASK_MAX 32
#define OCEOS_SEM_MAX 16
#define OCEOS_QUEUE_MAX 8

// OCEOS Priority Levels (higher number = higher priority)
#define LOW_PRIO 1
#define MED_PRIO 10
#define HIGH_PRIO 20
#define MAX_PRIO 255
#define CURRENT_PRIO 0

// OCEOS Task States
#define TASK_DORMANT 0
#define TASK_READY 1
#define TASK_RUNNING 2
#define TASK_WAITING 3
#define TASK_SUSPENDED 4
#define TASK_TERMINATED 5

// OCEOS Return Codes
#define SUCCESSFUL 0
#define INVALID_ID 1
#define INVALID_NAME 2
#define TOO_MANY 3
#define INCORRECT_STATE 4
#define INTERNAL_ERROR 5
#define INVALID_PRIORITY 6
#define TIMEOUT 7
#define RESOURCE_IN_USE 8

// OCEOS System States
#define SYSTEM_INIT 0
#define SYSTEM_RUNNING 1
#define SYSTEM_SHUTDOWN 2

// Test-specific constants
#define INVALID_ENTRY 0
#define TASK_ENTRY_0 1
#define TASK_ENTRY_1 2

// Semaphore indices for synchronization
#define SEM_LOCK 0
#define SEM_TASK_START_0 1
#define SEM_TASK_START_1 2
#define SEM_TASK0_FIN 3
#define SEM_TASK1_FIN 4
#define SEM_RUNNER_WAKE 5

// Task IDs
#define RUNNER_ID 0
#define TASK0_ID 1
#define TASK1_ID 2

// Common return codes for compatibility
#define RC_OK SUCCESSFUL
#define RC_AlrSuspd INCORRECT_STATE
#define INVALID_ID_VALUE 255

// OCEOS directive status for Promela
mtype = {
    DS_SUCCESSFUL,
    DS_INVALID_ID, 
    DS_INVALID_NAME,
    DS_TOO_MANY,
    DS_INCORRECT_STATE,
    DS_INTERNAL_ERROR,
    DS_INVALID_PRIORITY,
    DS_TIMEOUT,
    DS_RESOURCE_IN_USE
};

// OCEOS task states for Promela  
mtype = {
    TS_Dormant,
    TS_Ready,
    TS_Running,
    TS_Waiting,
    TS_Suspended,
    TS_Terminated,
    TS_Zombie
};
