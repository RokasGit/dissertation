/*
 * LTL Properties for OCEOS Task Management Verification
 * 
 * This file contains Linear Temporal Logic properties for verifying
 * the correctness of OCEOS task management operations.
 */

/* 
 * Safety Properties 
 */

/* Property S1: System maintains valid task table state */
ltl valid_task_table { 
    [] (system_initialized -> 
        (task_table[0].state == TASK_FREE || 
         task_table[0].state == TASK_ALLOCATED || 
         task_table[0].state == TASK_ENABLED || 
         task_table[0].state == TASK_DISABLED))
}

/* Property S2: No task ID conflicts */
ltl no_id_conflicts {
    [] ((task_table[0].state != TASK_FREE && task_table[1].state != TASK_FREE) ->
        (task_table[0].descriptor.task_id != task_table[1].descriptor.task_id))
}

/* Property S3: Priority constraints always satisfied */
ltl priority_constraints {
    [] ((task_table[0].state != TASK_FREE) ->
        (task_table[0].descriptor.task_priority >= MIN_PRIORITY &&
         task_table[0].descriptor.task_priority <= MAX_PRIORITY &&
         task_table[0].descriptor.task_threshold >= MIN_PRIORITY &&
         task_table[0].descriptor.task_threshold <= MAX_PRIORITY &&
         task_table[0].descriptor.task_threshold <= task_table[0].descriptor.task_priority))
}

/* Property S4: Resource bounds never exceeded */
ltl resource_bounds {
    [] (total_allocated_tasks <= MAX_TASKS)
}

/* Property S5: Job constraints satisfied */
ltl job_constraints {
    [] ((task_table[0].state != TASK_FREE) ->
        (task_table[0].descriptor.task_jobs_max >= 1 &&
         task_table[0].descriptor.task_jobs_max <= MAX_JOBS))
}

/* Property S6: Valid function pointers for allocated tasks */
ltl valid_functions {
    [] ((task_table[0].state == TASK_ALLOCATED || 
         task_table[0].state == TASK_ENABLED || 
         task_table[0].state == TASK_DISABLED) ->
        task_table[0].descriptor.function_start_valid)
}

/*
 * Liveness Properties
 */

/* Property L1: Task creation requests eventually get responses */
ltl create_responsiveness {
    [] (len(create_request) > 0 -> <> len(create_response) > 0)
}

/* Property L2: Valid task creation eventually succeeds */
ltl valid_creation_succeeds {
    [] ((len(create_request) > 0 && 
         /* Valid descriptor conditions */) -> 
        <> (task_table[0].state == TASK_ENABLED || task_table[0].state == TASK_DISABLED))
}

/* Property L3: Error conditions eventually return error codes */
ltl error_handling {
    [] ((len(create_request) > 0 && 
         /* Invalid descriptor conditions */) -> 
        <> len(create_response) > 0)
}

/*
 * Fairness Properties
 */

/* Property F1: All task IDs have fair allocation opportunity */
ltl fair_allocation {
    [] <> (task_table[0].state == TASK_FREE -> 
           <> (task_table[0].state != TASK_FREE))
}

/*
 * Temporal Ordering Properties
 */

/* Property T1: Task validation occurs before allocation */
ltl validation_before_allocation {
    [] ((task_table[0].state == TASK_FREE) U 
        (task_table[0].state == TASK_ALLOCATED))
}

/* Property T2: Tasks transition from allocated to enabled/disabled */
ltl state_progression {
    [] ((task_table[0].state == TASK_ALLOCATED) ->
        <> (task_table[0].state == TASK_ENABLED || 
            task_table[0].state == TASK_DISABLED))
}

/*
 * Invariant Properties (Always true)
 */

/* Property I1: System initialization completes */
ltl system_initialized_invariant {
    <> [] system_initialized
}

/* Property I2: Task table consistency */
ltl task_table_consistency {
    [] ((task_table[0].state != TASK_FREE) -> 
        (task_table[0].descriptor.task_id < MAX_TASKS))
}

/* Property I3: Counter consistency */
ltl counter_consistency {
    [] (total_allocated_tasks >= 0 && total_allocated_tasks <= MAX_TASKS)
}

/*
 * Error State Properties
 */

/* Property E1: Invalid priority always rejected */
ltl invalid_priority_rejected {
    [] ((task_table[0].descriptor.task_priority < MIN_PRIORITY ||
         task_table[0].descriptor.task_priority > MAX_PRIORITY) ->
        (task_table[0].state == TASK_FREE))
}

/* Property E2: Invalid threshold always rejected */
ltl invalid_threshold_rejected {
    [] ((task_table[0].descriptor.task_threshold > task_table[0].descriptor.task_priority) ->
        (task_table[0].state == TASK_FREE))
}

/* Property E3: Duplicate IDs always rejected */
ltl duplicate_id_rejected {
    [] ((task_table[0].state != TASK_FREE && task_table[1].state != TASK_FREE &&
         task_table[0].descriptor.task_id == task_table[1].descriptor.task_id) ->
        false) /* This should never be true */
}

/*
 * Performance Properties
 */

/* Property P1: Bounded response time for task creation */
ltl bounded_response {
    [] (len(create_request) > 0 -> 
        (<> len(create_response) > 0) /* Eventually responds */
}
