/**
 * @brief Unity test runner for OCEOS Task Manager Model scenario {0}
 */
void test_OceosTaskMgr_Scenario_{0}(void) {{
    OceosModelTaskMgr_Run_{0}(
        TaskCreate,
        TaskStart,
        TaskDelete,
        TaskSuspend,
        TaskResume,
        TaskSetPriority
    );
}}
