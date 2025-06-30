/*
 * OCEOS CreateTask Operation - Promela Model
 * 
 * This model represents the task creation operation in OCEOS RTOS,
 * based on the oceos_task_create() function and task_descriptor structure.
 * 
 * The model captures:
 * - Task descriptor validation
 * - Task allocation in system structures  
 * - Error conditions and return codes
 * - System state consistency
 */

#define MAX_TASKS 8         /* Maximum number of tasks in system */
#define MAX_PRIORITY 254    /* Highest priority value (lowest priority) */
#define MIN_PRIORITY 1      /* Lowest priority value (highest priority) */
#define MAX_JOBS 15         /* Maximum concurrent jobs per task */

/* Task states and return codes */
mtype = { TASK_FREE, TASK_ALLOCATED, TASK_ENABLED, TASK_DISABLED, TASK_INVALID,
          OCEOS_SUCCESS, ERR_T_ALREADY_ALLOCATED, ERR_T_PRIORITY_INVALID, 
          ERR_THRESHOLD_INVALID, ERR_THRESHOLD_WRONG, ERR_JOBS_MAX_INVALID,
          ERR_START_FUNCTION_BAD, ERR_AFFINITY_WRONG };

/* Task descriptor structure (simplified from OCEOS) */
typedef TaskDescriptor {
    bool function_start_valid;      /* Task start function validity */
    bool function_end_valid;        /* Task end function validity */
    byte task_id;                   /* Task ID (0-254) */
    byte task_jobs_max;             /* Max concurrent jobs (1-15) */
    byte task_priority;             /* Priority (1-254) */
    byte task_threshold;            /* Threshold priority */
    bool task_turned_on_initially;  /* Initial enable state */
    short time_deadline_microsecs;   /* Deadline constraint */
    short time_min_interval_microsecs; /* Minimum interval */
    bool uses_cpu_affinity;         /* CPU affinity flag */
    byte lowest_allowed_core_id;    /* Lowest core ID */
    byte highest_allowed_core_id;   /* Highest core ID */
};

/* System task table */
typedef TaskEntry {
    mtype state;                    /* Task state */
    TaskDescriptor desc_copy;       /* Task descriptor copy */
    byte allocated_jobs;            /* Currently allocated jobs */
};

/* Global system state */
TaskEntry task_table[MAX_TASKS];
byte total_allocated_tasks = 0;
byte total_allocated_jobs = 0;
bool system_initialized = false;

/* Channels for inter-process communication */
chan create_request = [1] of { TaskDescriptor };
chan create_response = [1] of { mtype };
chan validation_done = [1] of { mtype };
chan allocation_done = [1] of { bool };

/*
 * Task creation validation process
 * Validates task descriptor parameters according to OCEOS rules
 */
proctype TaskValidator(TaskDescriptor desc) {
    mtype result = OCEOS_SUCCESS;
    
    /* Validate task ID range */
    if :: (desc.task_id >= MAX_TASKS) -> 
            result = ERR_T_ALREADY_ALLOCATED;
            goto validation_complete;
       :: else -> skip;
    fi;
    
    /* Check if task ID already allocated */
    if :: (task_table[desc.task_id].state != TASK_FREE) ->
            result = ERR_T_ALREADY_ALLOCATED;
            goto validation_complete;
       :: else -> skip;
    fi;
    
    /* Validate priority range */
    if :: (desc.task_priority < MIN_PRIORITY || desc.task_priority > MAX_PRIORITY) ->
            result = ERR_T_PRIORITY_INVALID;
            goto validation_complete;
       :: else -> skip;
    fi;
    
    /* Validate threshold range and relationship to priority */
    if :: (desc.task_threshold < MIN_PRIORITY || desc.task_threshold > MAX_PRIORITY) ->
            result = ERR_THRESHOLD_INVALID;
            goto validation_complete;
       :: (desc.task_threshold > desc.task_priority) ->
            result = ERR_THRESHOLD_WRONG;
            goto validation_complete;
       :: else -> skip;
    fi;
    
    /* Validate maximum jobs */
    if :: (desc.task_jobs_max < 1 || desc.task_jobs_max > MAX_JOBS) ->
            result = ERR_JOBS_MAX_INVALID;
            goto validation_complete;
       :: else -> skip;
    fi;
    
    /* Validate start function */
    if :: (!desc.function_start_valid) ->
            result = ERR_START_FUNCTION_BAD;
            goto validation_complete;
       :: else -> skip;
    fi;
    
    /* Validate CPU affinity constraints */
    if :: (desc.uses_cpu_affinity) ->
            if :: (desc.lowest_allowed_core_id > desc.highest_allowed_core_id) ->
                    result = ERR_AFFINITY_WRONG;
                    goto validation_complete;
               :: else -> skip;
            fi;
       :: else -> skip;
    fi;
    
validation_complete:
    validation_done ! result;
}

/*
 * Task allocation process
 * Allocates system resources for validated task
 */
proctype TaskAllocator(TaskDescriptor desc) {
    atomic {
        /* Allocate task entry */
        task_table[desc.task_id].state = TASK_ALLOCATED;
        task_table[desc.task_id].desc_copy.function_start_valid = desc.function_start_valid;
        task_table[desc.task_id].desc_copy.function_end_valid = desc.function_end_valid;
        task_table[desc.task_id].desc_copy.task_id = desc.task_id;
        task_table[desc.task_id].desc_copy.task_jobs_max = desc.task_jobs_max;
        task_table[desc.task_id].desc_copy.task_priority = desc.task_priority;
        task_table[desc.task_id].desc_copy.task_threshold = desc.task_threshold;
        task_table[desc.task_id].desc_copy.task_turned_on_initially = desc.task_turned_on_initially;
        task_table[desc.task_id].desc_copy.time_deadline_microsecs = desc.time_deadline_microsecs;
        task_table[desc.task_id].desc_copy.time_min_interval_microsecs = desc.time_min_interval_microsecs;
        task_table[desc.task_id].desc_copy.uses_cpu_affinity = desc.uses_cpu_affinity;
        task_table[desc.task_id].desc_copy.lowest_allowed_core_id = desc.lowest_allowed_core_id;
        task_table[desc.task_id].desc_copy.highest_allowed_core_id = desc.highest_allowed_core_id;
        task_table[desc.task_id].allocated_jobs = 0;
        
        /* Update system counters */
        total_allocated_tasks++;
        
        /* Set initial state based on descriptor */
        if :: desc.task_turned_on_initially ->
                task_table[desc.task_id].state = TASK_ENABLED;
           :: else ->
                task_table[desc.task_id].state = TASK_DISABLED;
        fi;
    }
    
    /* Signal allocation completion */
    allocation_done ! true;
}

/*
 * Main task creation process
 * Orchestrates validation and allocation
 */
proctype CreateTask() {
    TaskDescriptor desc;
    mtype validation_result;
    byte test_count = 0;
    
    do
    :: create_request ? desc ->
        
        /* Start validation process */
        run TaskValidator(desc);
        
        /* Wait for validation result */
        validation_done ? validation_result;
        
        /* If validation successful, allocate task */
        if :: (validation_result == OCEOS_SUCCESS) ->
                run TaskAllocator(desc);
                allocation_done ? _;  /* Wait for allocation to complete */
           :: else -> skip; /* Error case - no allocation */
        fi;
        
        /* Send final result back */
        create_response ! validation_result;
        
        test_count++;
        if :: (test_count >= 4) -> break; /* Exit after 4 test cases */
           :: else -> skip;
        fi;
        
    od;
}

/*
 * Test harness process
 * Generates various task creation scenarios
 */
proctype TestHarness() {
    TaskDescriptor test_desc;
    mtype result;
    
    /* Test case 1: Valid task creation */
    test_desc.function_start_valid = true;
    test_desc.function_end_valid = true;
    test_desc.task_id = 0;
    test_desc.task_jobs_max = 2;
    test_desc.task_priority = 100;
    test_desc.task_threshold = 100;
    test_desc.task_turned_on_initially = true;
    test_desc.time_deadline_microsecs = 1000;
    test_desc.time_min_interval_microsecs = 500;
    test_desc.uses_cpu_affinity = false;
    test_desc.lowest_allowed_core_id = 0;
    test_desc.highest_allowed_core_id = 0;
    
    create_request ! test_desc;
    create_response ? result;
    assert(result == OCEOS_SUCCESS);
    assert(task_table[0].state == TASK_ENABLED);
    
    /* Test case 2: Invalid priority */
    test_desc.task_id = 1;
    test_desc.task_priority = 0; /* Invalid priority */
    
    create_request ! test_desc;
    create_response ? result;
    assert(result == ERR_T_PRIORITY_INVALID);
    assert(task_table[1].state == TASK_FREE);
    
    /* Test case 3: Duplicate task ID */
    test_desc.task_id = 0; /* Already allocated */
    test_desc.task_priority = 200; /* Valid priority */
    
    create_request ! test_desc;
    create_response ? result;
    assert(result == ERR_T_ALREADY_ALLOCATED);
    
    /* Test case 4: Invalid threshold relationship */
    test_desc.task_id = 2;
    test_desc.task_priority = 100;
    test_desc.task_threshold = 150; /* Lower priority than task priority - should be invalid */
    
    create_request ! test_desc;
    create_response ? result;
    assert(result == ERR_THRESHOLD_WRONG);
    assert(task_table[2].state == TASK_FREE);
    
    /* Test completed successfully */
    printf("All test cases completed successfully\n");
}

/*
 * System initialization
 */
init {
    byte i = 0;
    
    /* Initialize task table */
    do
    :: (i < MAX_TASKS) ->
        task_table[i].state = TASK_FREE;
        i++;
    :: (i >= MAX_TASKS) -> break;
    od;
    
    system_initialized = true;
    
    /* Start processes */
    run CreateTask();
    run TestHarness();
}

/* 
 * LTL Properties for verification
 */

/* Property 1: System consistency - allocated tasks must have valid descriptors */
#define valid_allocation (task_table[0].state == TASK_ALLOCATED || task_table[0].state == TASK_ENABLED || task_table[0].state == TASK_DISABLED) -> (task_table[0].desc_copy.task_priority >= MIN_PRIORITY && task_table[0].desc_copy.task_priority <= MAX_PRIORITY)

/* Property 2: No duplicate allocations */
#define no_duplicate_ids ((task_table[0].state != TASK_FREE) && (task_table[1].state != TASK_FREE)) -> (task_table[0].desc_copy.task_id != task_table[1].desc_copy.task_id)

/* Property 3: Priority ordering consistency */
#define priority_consistency (task_table[0].state != TASK_FREE) -> (task_table[0].desc_copy.task_threshold <= task_table[0].desc_copy.task_priority)

/* Property 4: Resource bounds */
#define resource_bounds (total_allocated_tasks <= MAX_TASKS)

/* Property 5: State machine validity */
#define state_validity (task_table[0].state == TASK_FREE || task_table[0].state == TASK_ALLOCATED || task_table[0].state == TASK_ENABLED || task_table[0].state == TASK_DISABLED)
