/* SPDX-License-Identifier: BSD-2-Clause */

/*
 * oceos-task-mgr-model.pml
 *
 * Copyright (C) 2025 Trinity College Dublin (www.tcd.ie)
 *
 * OCEOS Task Manager Promela Model
 * Formal model for OCEOS task management operations
 */

/*
 * OCEOS-specific constants and definitions
 */

#include "../../common/oceos.pml"
#define TASK_MAX 5 
#define SEM_MAX 6
#include "../../common/model.pml"

#include "task-mgr-h.pml"
#include "task-mgr-API.pml"

// Missing inline functions for synchronization and task management
inline setTask(task_id, rc) {
    // Enhanced OCEOS task setup with lifecycle tracking
    printf("@@@ %d CALL setTask %d\n", _pid, task_id);
    
    // Check if we can create more tasks
    if
    :: (oceos_task_count >= TASK_MAX) ->
        rc = false;
        printf("@@@ %d LOG setTask: Too many tasks\n", _pid);
    :: else ->
        // Initialize OCEOS task lifecycle
        task_created[task_id] = true;
        task_started[task_id] = false;
        task_terminated[task_id] = false;
        tasks[task_id].state = Dormant;
        oceos_task_count++;
        rc = true;
        printf("@@@ %d LOG setTask: Task %d created, count: %d\n", _pid, task_id, oceos_task_count);
    fi
}

inline TestSyncObtain(sem_id) {
    // Simple semaphore obtain operation  
    printf("@@@ %d SYNC OBTAIN %d\n", _pid, sem_id);
    semaphores[sem_id] = 1;
}

inline TestSyncRelease(sem_id) {
    // Simple semaphore release operation
    printf("@@@ %d SYNC RELEASE %d\n", _pid, sem_id);
    semaphores[sem_id] = 0;
}

inline outputDefines() {
    // Output model defines and constants
    printf("@@@ DEFINE TASK_MAX %d\n", TASK_MAX);
    printf("@@@ DEFINE SEM_MAX %d\n", SEM_MAX);
}

inline outputDeclarations() {
    // Output variable declarations
    printf("@@@ DECL byte createRC\n");
    printf("@@@ DECL byte startRC\n"); 
    printf("@@@ DECL byte deleteRC\n");
}

inline removeTask(task_id, rc) {
    // Enhanced OCEOS task removal with lifecycle tracking
    printf("@@@ %d CALL removeTask %d\n", _pid, task_id);
    
    if
    :: (task_created[task_id] == true) ->
        task_created[task_id] = false;
        task_started[task_id] = false;
        task_terminated[task_id] = true;
        tasks[task_id].state = Terminated;
        oceos_task_count--;
        rc = true;
        printf("@@@ %d LOG removeTask: Task %d removed, count: %d\n", _pid, task_id, oceos_task_count);
    :: else ->
        rc = false;
        printf("@@@ %d LOG removeTask: Task %d not found\n", _pid, task_id);
    fi
}

// Global variables for test scenarios
byte createRC;
byte startRC;
byte deleteRC;
byte suspendRC;
byte resumeRC;

// Task Create parameters
bool task_0_name;
byte task_0_id;
byte createPrio;
bool createValId;
bool createTask;

// Task Start parameters
byte taskEntry;
bool startValId;
bool startValEntry;
bool doubleStart;
bool startTask;

// Task Delete parameters
byte deleteId;
bool deleteTask;

// Task Suspend/Resume parameters
byte suspendId;
byte resumeId;
bool suspValId;
bool resumeValId;
bool doubleSuspend;
bool suspendSelf;
bool suspendTask;

// Priority test parameters
byte task_1_name;
byte task_1_id;
byte task_1_Entry;
bool testPrio;

// Declare OCEOS Scenario Types
mtype = {CreateDestroy, TaskStart, SuspResume, ChangePrio, ErrorConditions}

// Global scenario variable
mtype scenario;

// OCEOS System Management Variables (Step 1)
bool oceos_system_initialized = false;
bool oceos_scheduler_running = false;
byte oceos_current_task = 0;
byte oceos_task_count = 0;
byte oceos_active_tasks = 0;
bool oceos_clock_initialized = false;
byte oceos_system_time = 0;

inline chooseScenario() {
    // Initialize default values
    createTask = true;
    task_0_name = 1;
    createPrio = MED_PRIO;
    createValId = true;
    
    startTask = true;
    startValId = true;
    startValEntry = true;
    doubleStart = false;
    taskEntry = TASK_ENTRY_0;
    
    deleteTask = true;
    deleteId = INVALID_ID;
    
    suspendTask = false;
    suspendId = INVALID_ID;
    suspValId = true;
    doubleSuspend = false;
    suspendSelf = false;
    
    resumeId = INVALID_ID;
    resumeValId = true;
    
    testPrio = false;
    task_1_name = 2;
    task_1_Entry = TASK_ENTRY_1;

    if
    ::  scenario = CreateDestroy;
    ::  scenario = TaskStart;
    ::  scenario = SuspResume;
    ::  scenario = ChangePrio;
    ::  scenario = ErrorConditions;
    fi

    printf("@@@ %d LOG scenario %d\n", _pid, scenario);

    // Configure scenario-specific parameters
    if
    ::  scenario == CreateDestroy ->
            startTask = false; 
            deleteTask = false;
            if
            ::  task_0_name = 0;                        printf("@@@ %d LOG Create: Invalid Name\n", _pid);
            ::  createPrio = 0;                         printf("@@@ %d LOG Create: Invalid Priority (0)\n", _pid);
            ::  createPrio = MAX_PRIO;                  printf("@@@ %d LOG Create: Invalid Priority (MAX)\n", _pid);
            ::  createValId = false;                    printf("@@@ %d LOG Create: Invalid Id\n", _pid);
            ::  createTask = false; deleteTask = true;  printf("@@@ %d LOG Delete: Invalid Id\n", _pid);
            ::  deleteTask = true;                      printf("@@@ %d LOG Create: Success\n", _pid);
            fi

    ::  scenario == TaskStart ->
            startTask = false;
            if
            ::  startValId = false;         printf("@@@ %d LOG Start: Invalid Id\n", _pid);
            ::  startValEntry = false;      printf("@@@ %d LOG Start: Invalid Entry\n", _pid);
            ::  doubleStart = true;         printf("@@@ %d LOG Start: Task Already Started\n", _pid);
            ::  startTask = true;           printf("@@@ %d LOG Start: Success\n", _pid);
            fi

    ::  scenario == SuspResume ->
            suspendTask = true;
            if
            ::  startValEntry = false; startTask = false;   printf("@@@ %d LOG Suspend: Invalid State\n", _pid);
            ::  suspValId = false;                          printf("@@@ %d LOG Suspend: Invalid Id\n", _pid);
            ::  resumeValId = false;                        printf("@@@ %d LOG Resume: Invalid Id\n", _pid);
            ::  doubleSuspend = true;                       printf("@@@ %d LOG Suspend: Already Suspended\n", _pid);
            ::  suspendSelf = true; suspendTask = false;    printf("@@@ %d LOG Suspend: Self Suspend\n", _pid);
            ::  skip;                                       printf("@@@ %d LOG Suspend/Resume: Success\n", _pid);
            fi

    ::  scenario == ChangePrio ->
            testPrio = true;
            if
            ::  suspendSelf = true;         printf("@@@ %d LOG Priority: Self Suspend\n", _pid);
            ::  skip;                       printf("@@@ %d LOG Priority: Change Priority\n", _pid);
            fi

    ::  scenario == ErrorConditions ->
            // Test various error conditions
            if
            ::  createTask = false;         printf("@@@ %d LOG Error: No Create\n", _pid);
            ::  createValId = false;        printf("@@@ %d LOG Error: Invalid Create ID\n", _pid);
            ::  startValId = false;         printf("@@@ %d LOG Error: Invalid Start ID\n", _pid);
            fi
    fi
}

inline SuspendResume(suspId, resumeId) {
    bool repeated = false;

suspRepeat:
    // Suspend task
    printf("@@@ %d CALL oceos_task_suspend %d suspendRC\n", _pid, suspId);
    oceos_task_suspend(tasks[suspId], suspendRC);
    printf("@@@ %d SCALAR suspendRC %d\n", _pid, suspendRC);

    // Handle double suspend scenario
    if
    ::  doubleSuspend == true && repeated == false ->
            repeated = true;
            goto suspRepeat;
    ::  else
    fi

    // Resume task
    printf("@@@ %d CALL oceos_task_resume %d resumeRC\n", _pid, resumeId);
    oceos_task_resume(tasks[resumeId], resumeRC);
    printf("@@@ %d SCALAR resumeRC %d\n", _pid, resumeRC);
}

inline changePriority(taskid, prio, oldPrio, rc) {
    printf("@@@ %d CALL oceos_task_set_priority %d %d %d setPriorityRC\n", 
           _pid, taskid, prio, oldPrio);
    oceos_task_set_priority(taskid, prio, oldPrio, rc);
    printf("@@@ %d SCALAR setPriorityRC %d\n", _pid, rc);
}

proctype Runner(byte nid; byte taskid) {
    // Local variable declarations
    byte name;
    byte prio;
    byte threshold;
    byte jobs_max;
    bool fp_used;
    bool initially_enabled;
    bool setRC;
    bool runRC;
    
    assert(_priority == MED_PRIO);
    
    // Initialize runner task using parallel arrays
    task_nodeid[taskid] = nid;
    task_pmlid[taskid] = _pid;
    task_state[taskid] = Ready;

    // Task creation parameters
    name = task_0_name;
    prio = createPrio;
    threshold = createPrio;  // OCEOS uses threshold
    jobs_max = 5;
    fp_used = false;
    initially_enabled = true;

    // Task 0 Creation
    if 
    ::  createTask == true ->
        if
        ::  createValId == true ->
                setTask(task_0_id, setRC);
                if 
                ::  setRC == false ->
                        printf("@@@ %d CALL TooMany\n", _pid);
                ::  else
                fi
        ::  else ->
                task_0_id = 0;
                setRC = true;
        fi

        printf("@@@ %d CALL oceos_task_create %d %d createRC\n", 
               _pid, task_0_id, prio);
        
        oceos_task_create(task_0_id, prio, createRC);
        
        printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);
    ::  else
    fi

    // Task 0 Start
    if 
    ::  startTask == true ->
            byte startId;
            if
            ::  startValId == true ->
                    startId = task_0_id;
            ::  startValId == false ->
                    startId = INVALID_ID;
            fi

            bool doubleDone = false;
repeat_start:
            printf("@@@ %d CALL oceos_task_start %d startRC\n", _pid, startId);
            oceos_task_start(tasks[startId], startRC);
            printf("@@@ %d SCALAR startRC %d\n", _pid, startRC);
            
            if
            ::  startRC != RC_OK ->
                    TestSyncRelease(SEM_TASK0_FIN);
            ::  doubleStart == true ->
                    if 
                    ::  doubleDone == false ->
                            doubleDone = true;
                            goto repeat_start;
                    ::  else
                    fi
            ::  else
            fi
    ::  else -> skip
    fi

    // Priority testing
    if
    ::  testPrio == true ->
            // Create second task for priority testing
            setTask(task_1_id, setRC);
            printf("@@@ %d CALL oceos_task_create %d %d createRC\n", 
                   _pid, task_1_id, prio);
            oceos_task_create(task_1_id, prio, createRC);
            printf("@@@ %d SCALAR createRC %d\n", _pid, createRC);
            
            // Start second task
            printf("@@@ %d CALL oceos_task_start %d startRC\n", _pid, task_1_id);
            oceos_task_start(tasks[task_1_id], startRC);
            printf("@@@ %d SCALAR startRC %d\n", _pid, startRC);
    ::  else -> skip
    fi

    // Self suspend handling
    if
    ::  suspendSelf == true ->
            // Wait for task to self-suspend and then resume it
            printf("@@@ %d CALL WaitForSuspend %d\n", _pid, task_0_id);
            do
            ::  tasks[task_0_id].state == Suspended -> break;
            ::  else -> skip
            od

            printf("@@@ %d CALL oceos_task_resume %d resumeRC\n", _pid, task_0_id);
            oceos_task_resume(tasks[task_0_id], resumeRC);
            printf("@@@ %d SCALAR resumeRC %d\n", _pid, resumeRC);
    ::  else
    fi

    // Wait for task completion
    if 
    ::  startTask == true ->
            TestSyncObtain(SEM_TASK0_FIN);
    ::  else
    fi
    
    if
    ::  testPrio == true ->
            TestSyncObtain(SEM_TASK1_FIN);
    ::  else
    fi   

    // Suspend/Resume testing
    if
    ::  suspendTask == true ->
            if
            ::  suspValId == true ->
                    suspendId = task_0_id;
            ::  else
                    suspendId = 0;
            fi
            if
            ::  resumeValId == true ->
                    resumeId = task_0_id;
            ::  else
                    resumeId = 0;
            fi
            SuspendResume(suspendId, resumeId);
    ::  else 
    fi

    // Task deletion
    if
    ::  deleteTask == true -> 
            printf("@@@ %d CALL oceos_task_delete %d deleteRC\n", _pid, deleteId);
            oceos_task_delete(tasks[deleteId], deleteId, deleteRC);
            printf("@@@ %d SCALAR deleteRC %d\n", _pid, deleteRC);

            if
            ::  testPrio == true ->
                    printf("@@@ %d CALL oceos_task_delete %d deleteRC\n", _pid, task_1_id);
                    oceos_task_delete(tasks[task_1_id], task_1_id, deleteRC);
                    printf("@@@ %d SCALAR deleteRC %d\n", _pid, deleteRC);
            ::  else
            fi
    ::  else 
    fi

    // Cleanup
    removeTask(taskid, runRC);
    if
    ::  runRC == true ->
            task_state[taskid] = Zombie;
    ::  else
    fi
}

proctype Task0(byte taskId) {
    assert(_priority == MED_PRIO);
    assert(taskId < TASK_MAX);
    
    if
    ::  startTask == true ->
            TestSyncObtain(SEM_TASK_START_0);
            TestSyncRelease(SEM_TASK_START_0);

            tasks[taskId].pmlid = _pid;

            // Self suspend if required
            if
            ::  suspendSelf == true ->
                    printf("@@@ %d CALL oceos_task_suspend %d suspendRC\n", 
                           _pid, task_0_id);
                    oceos_task_suspend(tasks[task_0_id], suspendRC);
                    printf("@@@ %d SCALAR suspendRC %d\n", _pid, suspendRC);
            ::  else 
            fi
            
            // Priority testing
            if
            ::  testPrio == true ->
                    byte setPriorityRC;
                    byte old_prio = 1;
                    
                    printf("@@@ %d DECL byte priority 0\n", _pid);
                    changePriority(taskId, HIGH_PRIO, old_prio, setPriorityRC);
                    changePriority(taskId, CURRENT_PRIO, old_prio, setPriorityRC);
            ::  else -> skip
            fi
            
            // Signal completion
            TestSyncRelease(SEM_TASK0_FIN);
    ::  else -> skip
    fi
}

proctype Task1(byte taskId) {
    assert(_priority == MED_PRIO);
    assert(taskId < TASK_MAX);
    
    if
    ::  testPrio == true ->
            TestSyncObtain(SEM_TASK_START_1);
            TestSyncRelease(SEM_TASK_START_1);

            tasks[taskId].pmlid = _pid;
            
            // Priority manipulation
            byte setPriorityRC;
            byte old_prio = 1;
            
            printf("@@@ %d DECL byte priority 0\n", _pid);
            changePriority(taskId, LOW_PRIO, old_prio, setPriorityRC);
            changePriority(taskId, CURRENT_PRIO, old_prio, setPriorityRC);

            TestSyncRelease(SEM_TASK1_FIN);
    ::  else
    fi
}

proctype APITester() {
    // Dedicated process for comprehensive API testing scenarios
    printf("@@@ %d TASK APITester\n", _pid);
    
    #ifdef TEST_GEN
    // SCENARIO 5: Test task state transitions
    if
    ::  true ->
            printf("@@@ %d SCENARIO TaskStateTransitions\n", _pid);
            byte state_rc;
            TaskControlBlock test_task;
            test_task.nodeid = 3;
            
            // Create task (uses task_id parameter)
            printf("@@@ %d CALL oceos_task_create %d %d state_rc\n", _pid, test_task.nodeid, MED_PRIO);
            oceos_task_create(test_task.nodeid, MED_PRIO, state_rc);
            printf("@@@ %d ASSERT_EQ %d %d TaskCreated\n", _pid, state_rc, SUCCESSFUL);
            assert(state_rc == SUCCESSFUL);
            
            // Start task (uses task structure)
            printf("@@@ %d CALL oceos_task_start %d state_rc\n", _pid, test_task.nodeid);
            oceos_task_start(test_task, state_rc);
            printf("@@@ %d ASSERT_EQ %d %d TaskStarted\n", _pid, state_rc, SUCCESSFUL);
            assert(state_rc == SUCCESSFUL);
            
            // Suspend task (uses task structure)
            printf("@@@ %d CALL oceos_task_suspend %d state_rc\n", _pid, test_task.nodeid);
            oceos_task_suspend(test_task, state_rc);
            printf("@@@ %d ASSERT_EQ %d %d TaskSuspended\n", _pid, state_rc, SUCCESSFUL);
            assert(state_rc == SUCCESSFUL);
            
            // Resume task (uses task structure)
            printf("@@@ %d CALL oceos_task_resume %d state_rc\n", _pid, test_task.nodeid);
            oceos_task_resume(test_task, state_rc);
            printf("@@@ %d ASSERT_EQ %d %d TaskResumed\n", _pid, state_rc, SUCCESSFUL);
            assert(state_rc == SUCCESSFUL);
            
            // Delete task (check the API signature first)
            printf("@@@ %d CALL oceos_task_delete %d state_rc\n", _pid, test_task.nodeid);
            oceos_task_delete(test_task, test_task.nodeid, state_rc);
            printf("@@@ %d ASSERT_EQ %d %d TaskDeleted\n", _pid, state_rc, SUCCESSFUL);
            assert(state_rc == SUCCESSFUL);
    ::  else
    fi
    
    // SCENARIO 6: Test priority validation
    if
    ::  true ->
            printf("@@@ %d SCENARIO PriorityValidation\n", _pid);
            byte prio_rc;
            TaskControlBlock prio_task;
            prio_task.nodeid = 4;
            
            // Test zero priority (invalid) - create uses task_id
            printf("@@@ %d CALL oceos_task_create %d %d prio_rc\n", _pid, prio_task.nodeid, 0);
            oceos_task_create(prio_task.nodeid, 0, prio_rc);  // Priority 0 should be invalid
            printf("@@@ %d ASSERT_EQ %d %d PriorityInvalid\n", _pid, prio_rc, INVALID_PRIORITY);
            assert(prio_rc == INVALID_PRIORITY);
            
            // Test priority beyond max (invalid) - create uses task_id
            printf("@@@ %d CALL oceos_task_create %d %d prio_rc\n", _pid, prio_task.nodeid, 256);
            oceos_task_create(prio_task.nodeid, 256, prio_rc);  // Priority > MAX_PRIO
            printf("@@@ %d ASSERT_EQ %d %d PriorityInvalid\n", _pid, prio_rc, INVALID_PRIORITY);
            assert(prio_rc == INVALID_PRIORITY);
    ::  else
    fi
    #endif
}

proctype System() {
    // Enhanced OCEOS system management process
    printf("@@@ %d TASK System\n", _pid);
    
    // Initialize OCEOS system
    oceos_system_initialized = true;
    oceos_scheduler_running = true;
    oceos_task_count = 0;
    oceos_active_tasks = 0;
    
    printf("@@@ %d LOG System: OCEOS initialized\n", _pid);
    
    // Continuous system monitoring
    do
    :: (oceos_scheduler_running == true) ->
        // Monitor task states and system health
        byte i;
        oceos_active_tasks = 0;
        for (i : 0 .. (TASK_MAX-1)) {
            if
            :: (task_created[i] == true && task_started[i] == true && 
                tasks[i].state != Terminated && tasks[i].state != Zombie) ->
                oceos_active_tasks++;
            :: else -> skip;
            fi
        }
        
        // Update current running task
        for (i : 0 .. (TASK_MAX-1)) {
            if
            :: (tasks[i].state == Running) ->
                oceos_current_task = i;
                break;
            :: else -> skip;
            fi
        }
        
        // System maintenance tasks
        if
        :: (oceos_active_tasks == 0 && oceos_task_count > 0) ->
            printf("@@@ %d LOG System: All tasks completed\n", _pid);
            oceos_scheduler_running = false;
        :: else -> skip;
        fi
    :: else -> break;
    od
    
    printf("@@@ %d LOG System: OCEOS shutdown\n", _pid);
}

proctype Clock() {
    // Enhanced OCEOS clock management process
    printf("@@@ %d TASK Clock\n", _pid);
    
    // Initialize OCEOS clock
    oceos_clock_initialized = true;
    oceos_system_time = 0;
    
    printf("@@@ %d LOG Clock: OCEOS clock initialized\n", _pid);
    
    // Continuous clock operations
    do
    :: (oceos_system_initialized == true && oceos_scheduler_running == true) ->
        // Increment system time
        oceos_system_time++;
        
        // Handle periodic tasks and timeouts
        byte i;
        for (i : 0 .. (TASK_MAX-1)) {
            if
            :: (tasks[i].state == Waiting) ->
                // Could implement timeout handling here
                printf("@@@ %d LOG Clock: Task %d waiting\n", _pid, i);
            :: else -> skip;
            fi
        }
        
        // Clock tick processing
        if
        :: (oceos_system_time % 10 == 0) ->
            printf("@@@ %d LOG Clock: Tick %d\n", _pid, oceos_system_time);
        :: else -> skip;
        fi
        
        // Exit condition
        if
        :: (oceos_scheduler_running == false) -> break;
        :: else -> skip;
        fi
    :: else -> break;
    od
    
    printf("@@@ %d LOG Clock: OCEOS clock stopped\n", _pid);
}

init {
    printf("OCEOS Task Manager Model running.\n");
    printf("Setup...\n");

    printf("@@@ %d NAME OCEOS_Task_Manager_TestGen\n", _pid)

    outputDefines();
    outputDeclarations();

    chooseScenario();
    printf("@@@ %d INIT\n", _pid);

    printf("Run...\n");
    set_priority(_pid, MED_PRIO);

    // SCENARIO 1: Test invalid task ID handling
    #ifdef TEST_GEN
    if
    ::  true -> 
            printf("@@@ %d SCENARIO InvalidTaskID\n", _pid);
            byte invalid_rc;
            byte invalid_task_id = 255;  // Invalid task ID
            printf("@@@ %d CALL oceos_task_create %d %d invalid_rc\n", _pid, invalid_task_id, MED_PRIO);
            oceos_task_create(invalid_task_id, MED_PRIO, invalid_rc);
            printf("@@@ %d SCALAR invalid_rc %d\n", _pid, invalid_rc);
            printf("@@@ %d ASSERT_EQ %d %d InvalidID\n", _pid, invalid_rc, INVALID_ID);
            assert(invalid_rc == INVALID_ID);  // Should return INVALID_ID
    ::  else
    fi
    #endif

    if 
    ::  startTask == true ->
            printf("@@@ %d DEF TASK_0 %d\n", _pid, startTask);
    ::  else
    fi
    if
    ::  testPrio == true ->
            printf("@@@ %d DEF TASK_1 %d\n", _pid, testPrio);
    ::  else
    fi

    // SCENARIO 2: Test valid task creation with boundary conditions
    #ifdef TEST_GEN
    if  
    ::  true ->
            printf("@@@ %d SCENARIO BoundaryPriority\n", _pid);
            byte boundary_rc;
            byte boundary_task_id = 1;
            printf("@@@ %d CALL oceos_task_create %d %d boundary_rc\n", _pid, boundary_task_id, MAX_PRIO);
            oceos_task_create(boundary_task_id, MAX_PRIO, boundary_rc);  // Max priority
            printf("@@@ %d SCALAR boundary_rc %d\n", _pid, boundary_rc);
            printf("@@@ %d ASSERT_EQ %d %d Successful\n", _pid, boundary_rc, SUCCESSFUL);
            assert(boundary_rc == SUCCESSFUL);  // Should succeed
    ::  else
    fi
    #endif

    // SCENARIO 3: Test resource exhaustion (too many tasks)
    #ifdef TEST_GEN
    if
    ::  true ->
            printf("@@@ %d SCENARIO ResourceExhaustion\n", _pid);
            byte exhaust_rc;
            byte task_count = 0;
            // Try to create more tasks than TASK_MAX allows
            do
            :: (task_count < TASK_MAX + 2) ->
                    printf("@@@ %d CALL oceos_task_create %d %d exhaust_rc\n", _pid, task_count, MED_PRIO);
                    oceos_task_create(task_count, MED_PRIO, exhaust_rc);
                    printf("@@@ %d SCALAR exhaust_rc %d\n", _pid, exhaust_rc);
                    if
                    :: (task_count >= TASK_MAX) ->
                            printf("@@@ %d ASSERT_EQ %d %d TooMany\n", _pid, exhaust_rc, TOO_MANY);
                            assert(exhaust_rc == TOO_MANY);  // Should return TOO_MANY
                            break;
                    :: else -> skip;
                    fi
                    task_count++;
            :: else -> break;
            od
    ::  else
    fi
    #endif

    // SCENARIO 4: Test suspend/resume of non-existent task
    #ifdef TEST_GEN
    if
    ::  true ->
            printf("@@@ %d SCENARIO SuspendNonExistent\n", _pid);
            byte suspend_rc;
            TaskControlBlock suspend_task;
            suspend_task.nodeid = 99;  // Non-existent task
            printf("@@@ %d CALL oceos_task_suspend %d suspend_rc\n", _pid, suspend_task.nodeid);
            oceos_task_suspend(suspend_task, suspend_rc);
            printf("@@@ %d SCALAR suspend_rc %d\n", _pid, suspend_rc);
            printf("@@@ %d ASSERT_EQ %d %d InvalidID\n", _pid, suspend_rc, INVALID_ID);
            assert(suspend_rc == INVALID_ID);  // Should return INVALID_ID
    ::  else
    fi
    #endif

    run System();
    run Clock();
    run APITester();
    
    TestSyncRelease(SEM_LOCK);
    
    run Runner(0, RUNNER_ID) priority MED_PRIO;
    run Task0(TASK0_ID) priority MED_PRIO;
    run Task1(TASK1_ID) priority MED_PRIO;

    // Wait for all processes to complete
    _nr_pr == 1;

    // OCEOS System Shutdown Sequence (Step 5)
    printf("@@@ %d LOG System: Initiating OCEOS shutdown\n", _pid);
    oceos_scheduler_running = false;
    oceos_system_initialized = false;
    oceos_clock_initialized = false;
    
    // Final system state logging
    printf("@@@ %d LOG System: Active tasks: %d\n", _pid, oceos_active_tasks);
    printf("@@@ %d LOG System: Total tasks created: %d\n", _pid, oceos_task_count);
    printf("@@@ %d LOG System: Final time: %d\n", _pid, oceos_system_time);

    #ifdef TEST_GEN
    assert(false);
    #endif

    printf("OCEOS Task Manager Model finished!\n")
}
