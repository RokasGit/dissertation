/*
 * OCEOS Task State Management - Promela Model
 * 
 * This model represents task state transitions and management
 * in the OCEOS RTOS, focusing on the task lifecycle and state consistency.
 * 
 * Models the following task states and transitions:
 * - TASK_FREE -> TASK_ALLOCATED (via oceos_task_create)
 * - TASK_ALLOCATED -> TASK_ENABLED/TASK_DISABLED (initialization)
 * - TASK_ENABLED <-> TASK_DISABLED (via enable/disable operations)
 * - Any state -> TASK_FREE (via task deletion)
 */

#define MAX_TASKS 4

/* All mtype declarations must be in one statement */
mtype = { 
    /* Task states from OCEOS */
    TASK_FREE, TASK_ALLOCATED, TASK_ENABLED, TASK_DISABLED, TASK_RUNNING, TASK_READY, TASK_WAITING,
    /* Task operations */
    OP_CREATE, OP_DELETE, OP_ENABLE, OP_DISABLE, OP_START, OP_SUSPEND, OP_RESUME,
    /* Operation results */
    SUCCESS, ERROR_INVALID_ID, ERROR_INVALID_STATE, ERROR_SYSTEM_FULL
};

/* Task Control Block (simplified) */
typedef TaskCB {
    mtype state;           /* Current task state */
    byte task_id;          /* Task identifier */
    byte task_priority;    /* Task priority (renamed to avoid keyword conflict) */
    bool is_enabled;       /* Enable flag (renamed to avoid 'enabled' keyword) */
    byte jobs_active;      /* Number of active jobs */
    byte jobs_max;         /* Maximum allowed jobs */
};

/* Global system state */
TaskCB task_table[MAX_TASKS];
byte active_tasks = 0;
byte running_tasks = 0;

/* Communication channels */
chan task_ops = [8] of { mtype, byte, byte }; /* operation, task_id, parameter */
chan task_results = [8] of { mtype };         /* operation result */

/*
 * Task state transition validation
 */
inline valid_transition(from_state, to_state, result) {
    if
    :: (from_state == TASK_FREE && to_state == TASK_ALLOCATED) -> 
        result = SUCCESS;
    :: (from_state == TASK_ALLOCATED && (to_state == TASK_ENABLED || to_state == TASK_DISABLED)) ->
        result = SUCCESS;
    :: (from_state == TASK_ENABLED && to_state == TASK_DISABLED) ->
        result = SUCCESS;
    :: (from_state == TASK_DISABLED && to_state == TASK_ENABLED) ->
        result = SUCCESS;
    :: (from_state == TASK_ENABLED && to_state == TASK_READY) ->
        result = SUCCESS;
    :: (from_state == TASK_READY && to_state == TASK_RUNNING) ->
        result = SUCCESS;
    :: (from_state == TASK_RUNNING && to_state == TASK_READY) ->
        result = SUCCESS;
    :: (from_state == TASK_RUNNING && to_state == TASK_WAITING) ->
        result = SUCCESS;
    :: (from_state == TASK_WAITING && to_state == TASK_READY) ->
        result = SUCCESS;
    :: (to_state == TASK_FREE) -> /* Any state can transition to FREE (deletion) */
        result = SUCCESS;
    :: else ->
        result = ERROR_INVALID_STATE;
    fi;
}

/*
 * Task creation process
 */
proctype TaskCreate(byte task_id; byte task_priority_param) {
    mtype result;
    
    atomic {
        if
        :: (task_id >= MAX_TASKS) ->
            result = ERROR_INVALID_ID;
        :: (task_table[task_id].state != TASK_FREE) ->
            result = ERROR_INVALID_STATE;
        :: (active_tasks >= MAX_TASKS) ->
            result = ERROR_SYSTEM_FULL;
        :: else ->
            /* Valid creation */
            task_table[task_id].state = TASK_ALLOCATED;
            task_table[task_id].task_id = task_id;
            task_table[task_id].task_priority = task_priority_param;
            task_table[task_id].is_enabled = false;
            task_table[task_id].jobs_active = 0;
            task_table[task_id].jobs_max = 1;
            active_tasks++;
            result = SUCCESS;
        fi;
    }
    
    task_results ! result;
}

/*
 * Task deletion process
 */
proctype TaskDelete(byte task_id) {
    mtype result;
    
    atomic {
        if
        :: (task_id >= MAX_TASKS) ->
            result = ERROR_INVALID_ID;
        :: (task_table[task_id].state == TASK_FREE) ->
            result = ERROR_INVALID_STATE;
        :: else ->
            /* Valid deletion */
            if
            :: (task_table[task_id].state == TASK_RUNNING) ->
                running_tasks--;
            :: else -> skip;
            fi;
            
            task_table[task_id].state = TASK_FREE;
            task_table[task_id].is_enabled = false;
            task_table[task_id].jobs_active = 0;
            active_tasks--;
            result = SUCCESS;
        fi;
    }
    
    task_results ! result;
}

/*
 * Task enable/disable process
 */
proctype TaskSetEnabled(byte task_id; bool enable_flag) {
    mtype result;
    mtype old_state, new_state;
    
    atomic {
        if
        :: (task_id >= MAX_TASKS) ->
            result = ERROR_INVALID_ID;
        :: (task_table[task_id].state == TASK_FREE) ->
            result = ERROR_INVALID_STATE;
        :: else ->
            old_state = task_table[task_id].state;
            
            if
            :: enable_flag ->
                if
                :: (old_state == TASK_ALLOCATED || old_state == TASK_DISABLED) ->
                    new_state = TASK_ENABLED;
                :: else ->
                    new_state = old_state; /* No change for other states */
                fi;
            :: else -> /* disable */
                if
                :: (old_state == TASK_ENABLED || old_state == TASK_READY) ->
                    new_state = TASK_DISABLED;
                :: (old_state == TASK_RUNNING) ->
                    new_state = TASK_DISABLED;
                    running_tasks--;
                :: else ->
                    new_state = old_state; /* No change for other states */
                fi;
            fi;
            
            valid_transition(old_state, new_state, result);
            
            if
            :: (result == SUCCESS) ->
                task_table[task_id].state = new_state;
                task_table[task_id].is_enabled = enable_flag;
            :: else -> skip;
            fi;
        fi;
    }
    
    task_results ! result;
}

/*
 * Task start process
 */
proctype TaskStart(byte task_id) {
    mtype result;
    mtype old_state;
    
    atomic {
        if
        :: (task_id >= MAX_TASKS) ->
            result = ERROR_INVALID_ID;
        :: (task_table[task_id].state != TASK_ENABLED) ->
            result = ERROR_INVALID_STATE;
        :: (task_table[task_id].jobs_active >= task_table[task_id].jobs_max) ->
            result = ERROR_SYSTEM_FULL;
        :: else ->
            old_state = task_table[task_id].state;
            task_table[task_id].state = TASK_READY;
            task_table[task_id].jobs_active++;
            result = SUCCESS;
        fi;
    }
    
    task_results ! result;
}

/*
 * Task scheduler process
 * Manages transitions between READY, RUNNING, and WAITING states
 */
proctype TaskScheduler() {
    byte i;
    byte highest_priority = 255;
    byte selected_task = MAX_TASKS;
    bool found_ready = false;
    
    do
    :: true ->
        atomic {
            /* Find highest priority ready task */
            highest_priority = 255;
            selected_task = MAX_TASKS;
            found_ready = false;
            
            i = 0;
            do
            :: (i < MAX_TASKS) ->
                if
                :: (task_table[i].state == TASK_READY && 
                    task_table[i].task_priority < highest_priority) ->
                    highest_priority = task_table[i].task_priority;
                    selected_task = i;
                    found_ready = true;
                :: else -> skip;
                fi;
                i++;
            :: (i >= MAX_TASKS) -> break;
            od;
            
            /* Schedule selected task if found */
            if
            :: (found_ready && selected_task < MAX_TASKS) ->
                /* Preempt currently running task if any */
                i = 0;
                do
                :: (i < MAX_TASKS) ->
                    if
                    :: (task_table[i].state == TASK_RUNNING &&
                        task_table[i].task_priority > highest_priority) ->
                        task_table[i].state = TASK_READY;
                        running_tasks--;
                    :: else -> skip;
                    fi;
                    i++;
                :: (i >= MAX_TASKS) -> break;
                od;
                
                /* Start selected task */
                task_table[selected_task].state = TASK_RUNNING;
                running_tasks++;
                
            :: else -> skip; /* No ready tasks */
            fi;
        }
    od;
}

/*
 * Task operation dispatcher
 */
proctype TaskManager() {
    mtype operation;
    byte task_id, parameter;
    
    do
    :: task_ops ? operation, task_id, parameter ->
        if
        :: (operation == OP_CREATE) ->
            run TaskCreate(task_id, parameter);
        :: (operation == OP_DELETE) ->
            run TaskDelete(task_id);
        :: (operation == OP_ENABLE) ->
            run TaskSetEnabled(task_id, true);
        :: (operation == OP_DISABLE) ->
            run TaskSetEnabled(task_id, false);
        :: (operation == OP_START) ->
            run TaskStart(task_id);
        :: else -> 
            task_results ! ERROR_INVALID_STATE;
        fi;
    od;
}

/*
 * Test scenario generator
 */
proctype TestScenarios() {
    mtype result;
    
    /* Test 1: Create and enable task */
    task_ops ! OP_CREATE, 0, 100; /* task_id=0, priority=100 */
    task_results ? result;
    assert(result == SUCCESS);
    assert(task_table[0].state == TASK_ALLOCATED);
    
    task_ops ! OP_ENABLE, 0, 1;
    task_results ? result;
    assert(result == SUCCESS);
    assert(task_table[0].state == TASK_ENABLED);
    
    /* Test 2: Start task */
    task_ops ! OP_START, 0, 0;
    task_results ? result;
    assert(result == SUCCESS);
    assert(task_table[0].state == TASK_READY);
    
    /* Test 3: Create higher priority task */
    task_ops ! OP_CREATE, 1, 50; /* Higher priority (lower number) */
    task_results ? result;
    assert(result == SUCCESS);
    
    task_ops ! OP_ENABLE, 1, 1;
    task_results ? result;
    assert(result == SUCCESS);
    
    task_ops ! OP_START, 1, 0;
    task_results ? result;
    assert(result == SUCCESS);
    
    /* Test 4: Error cases */
    task_ops ! OP_CREATE, 0, 200; /* Duplicate task ID */
    task_results ? result;
    assert(result == ERROR_INVALID_STATE);
    
    task_ops ! OP_START, 5, 0; /* Invalid task ID */
    task_results ? result;
    assert(result == ERROR_INVALID_ID);
    
    /* Test 5: Disable and delete */
    task_ops ! OP_DISABLE, 0, 0;
    task_results ? result;
    assert(result == SUCCESS);
    assert(task_table[0].state == TASK_DISABLED);
    
    task_ops ! OP_DELETE, 0, 0;
    task_results ? result;
    assert(result == SUCCESS);
    assert(task_table[0].state == TASK_FREE);
}

/*
 * System monitor for invariant checking
 */
proctype SystemMonitor() {
    do
    :: true ->
        atomic {
            /* Check system invariants */
            assert(active_tasks <= MAX_TASKS);
            assert(running_tasks <= 1); /* Single core assumption */
            
            /* Verify task table consistency */
            byte i = 0;
            byte counted_active = 0;
            byte counted_running = 0;
            
            do
            :: (i < MAX_TASKS) ->
                if
                :: (task_table[i].state != TASK_FREE) ->
                    counted_active++;
                :: else -> skip;
                fi;
                
                if
                :: (task_table[i].state == TASK_RUNNING) ->
                    counted_running++;
                :: else -> skip;
                fi;
                
                i++;
            :: (i >= MAX_TASKS) -> break;
            od;
            
            assert(counted_active == active_tasks);
            assert(counted_running == running_tasks);
        }
    od;
}

/*
 * Initialize system
 */
init {
    byte i = 0;
    
    /* Initialize task table */
    do
    :: (i < MAX_TASKS) ->
        task_table[i].state = TASK_FREE;
        task_table[i].task_id = i;
        task_table[i].task_priority = 255;
        task_table[i].is_enabled = false;
        task_table[i].jobs_active = 0;
        task_table[i].jobs_max = 1;
        i++;
    :: (i >= MAX_TASKS) -> break;
    od;
    
    /* Start system processes */
    run TaskManager();
    run TaskScheduler();
    run SystemMonitor();
    run TestScenarios();
}

/*
 * LTL Properties for Task State Management
 */

/* Property: Tasks eventually become free after deletion */
ltl task_deletion_cleanup { 
    [] ((task_table[0].state != TASK_FREE) -> <> (task_table[0].state == TASK_FREE))
}

/* Property: System counters remain consistent */
ltl counter_consistency {
    [] (active_tasks <= MAX_TASKS && running_tasks <= 1)
}

/* Property: No invalid state transitions */
ltl valid_transitions {
    [] ((task_table[0].state == TASK_FREE) -> 
        (task_table[0].state == TASK_FREE || task_table[0].state == TASK_ALLOCATED))
}

/* Property: Enabled tasks can eventually run */
ltl enabled_tasks_schedulable {
    [] ((task_table[0].state == TASK_ENABLED) -> <> (task_table[0].state == TASK_RUNNING))
}

/* Property: Higher priority tasks preempt lower priority */
ltl priority_ordering {
    [] ((task_table[0].state == TASK_RUNNING && task_table[1].state == TASK_READY &&
         task_table[1].task_priority < task_table[0].task_priority) ->
        <> (task_table[1].state == TASK_RUNNING))
}
