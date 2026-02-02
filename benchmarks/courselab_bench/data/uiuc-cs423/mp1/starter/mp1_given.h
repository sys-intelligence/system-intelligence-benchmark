#ifndef __MP1_GIVEN_INCLUDE__
#define __MP1_GIVEN_INCLUDE__

#include <linux/pid.h>
#include <linux/sched.h>

#define find_task_by_pid(nr) pid_task(find_vpid(nr), PIDTYPE_PID)

// Query the CPU time for the given PID.
// Parameters:
//   pid: [In] The process to query.
//   cpu_use: [Out] The CPU time of the process.
// Return:
//   Return 0 on succeed. Return -1 if error occured or the process is dead.
int get_cpu_use(int pid, unsigned long *cpu_use)
{
    struct task_struct* task = NULL;
    
    // Prevent race condition on the `task` variable
    rcu_read_lock();
    task = find_task_by_pid(pid);

    if (task != NULL) {  
        *cpu_use = task->utime;
        // Release the lock
        rcu_read_unlock();
        return 0;
    }
    else {
        *cpu_use = 0;
        rcu_read_unlock();
        return -1;
    }
}

#endif
