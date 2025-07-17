/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * task-mgr-API.pml
 *
 * Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
 *
 * OCEOS Task Manager API Definitions
 * Promela inline functions for OCEOS task management API
 */

/*
 * OCEOS Task Create API
 * Creates a new task with specified parameters
 */
inline oceos_task_create(task_id, prio, result) {
    atomic {
        if
        :: (task_id == 0 || task_id >= TASK_MAX) ->
            result = INVALID_ID;
        :: (task_created[task_id] == true) ->
            result = TOO_MANY;
        :: (prio == 0 || prio > MAX_PRIO) ->
            result = INVALID_PRIORITY;
        :: else ->
            /* Valid creation */
            task_priority[task_id] = prio;
            task_threshold[task_id] = prio;  // Use same value
            task_state[task_id] = Dormant;
            task_enabled[task_id] = true;
            task_created[task_id] = true;
            task_started[task_id] = false;
            task_suspended[task_id] = false;
            task_terminated[task_id] = false;
            result = SUCCESSFUL;
        fi
    }
}

/*
 * OCEOS Task Start API
 * Starts a previously created task
 */
inline oceos_task_start(task, result) {
    atomic {
        byte tid = task.nodeid; /* Use nodeid as task identifier */
        if
        :: (tid == 0 || tid >= TASK_MAX) ->
            result = INVALID_ID;
        :: (task_created[tid] == false) ->
            result = INVALID_ID;
        :: (task_started[tid] == true) ->
            result = INCORRECT_STATE;
        :: (task_terminated[tid] == true) ->
            result = INCORRECT_STATE;
        :: else ->
            /* Valid start */
            task_started[tid] = true;
            tasks[tid].state = Ready;
            result = SUCCESSFUL;
        fi
    }
}

/*
 * OCEOS Task Delete API
 * Deletes a task
 */
inline oceos_task_delete(task, tid, result) {
    atomic {
        if
        :: (tid == 0 || tid >= TASK_MAX) ->
            result = INVALID_ID;
        :: (task_created[tid] == false) ->
            result = INVALID_ID;
        :: else ->
            /* Valid deletion */
            tasks[tid].state = Terminated;
            task_terminated[tid] = true;
            task_created[tid] = false;
            task_started[tid] = false;
            task_suspended[tid] = false;
            result = SUCCESSFUL;
        fi
    }
}

/*
 * OCEOS Task Suspend API
 * Suspends a running task
 */
inline oceos_task_suspend(task, result) {
    atomic {
        byte tid = task.nodeid;
        if
        :: (tid == 0 || tid >= TASK_MAX) ->
            result = INVALID_ID;
        :: (task_created[tid] == false) ->
            result = INVALID_ID;
        :: (task_started[tid] == false) ->
            result = INCORRECT_STATE;
        :: (task_suspended[tid] == true) ->
            result = INCORRECT_STATE;
        :: (task_terminated[tid] == true) ->
            result = INCORRECT_STATE;
        :: else ->
            /* Valid suspension */
            task_suspended[tid] = true;
            tasks[tid].state = Suspended;
            result = SUCCESSFUL;
        fi
    }
}

/*
 * OCEOS Task Resume API
 * Resumes a suspended task
 */
inline oceos_task_resume(task, result) {
    atomic {
        byte tid = task.nodeid;
        if
        :: (tid == 0 || tid >= TASK_MAX) ->
            result = INVALID_ID;
        :: (task_created[tid] == false) ->
            result = INVALID_ID;
        :: (task_started[tid] == false) ->
            result = INCORRECT_STATE;
        :: (task_suspended[tid] == false) ->
            result = INCORRECT_STATE;
        :: (task_terminated[tid] == true) ->
            result = INCORRECT_STATE;
        :: else ->
            /* Valid resume */
            task_suspended[tid] = false;
            tasks[tid].state = Ready;
            result = SUCCESSFUL;
        fi
    }
}

/*
 * OCEOS Task Set Priority API
 * Changes task priority
 */
inline oceos_task_set_priority(tid, new_priority, old_priority, result) {
    atomic {
        if
        :: (tid == 0 || tid >= TASK_MAX) ->
            result = INVALID_ID;
        :: (task_created[tid] == false) ->
            result = INVALID_ID;
        :: (new_priority == 0 || new_priority > MAX_PRIO) ->
            result = INVALID_PRIORITY;
        :: else ->
            /* Valid priority change */
            old_priority = task_priority[tid];
            task_priority[tid] = new_priority;
            result = SUCCESSFUL;
        fi
    }
}

/*
 * Helper function to get task state
 */
inline getTaskState(tid, state) {
    if
    :: (tid == 0 || tid >= TASK_MAX) ->
        state = Invalid;
    :: else ->
        state = tasks[tid].state;
    fi
}

/*
 * Helper function to check if task exists
 */
inline taskExists(tid, exists) {
    if
    :: (tid == 0 || tid >= TASK_MAX) ->
        exists = false;
    :: else ->
        exists = task_created[tid];
    fi
}
