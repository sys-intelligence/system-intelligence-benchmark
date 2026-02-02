#ifndef __MP3_GIVEN_INCLUDE__
#define __MP3_GIVEN_INCLUDE__

#include <linux/pid.h>
#include <linux/sched.h>

struct task_struct* find_task_by_pid(unsigned int nr)
{
    struct task_struct* task = NULL;
    rcu_read_lock();
    task=pid_task(find_vpid(nr), PIDTYPE_PID);
    rcu_read_unlock();
    if (task == NULL)
        printk(KERN_INFO "find_task_by_pid: couldnt find pid %d\n", nr);
    return task;
}

// THIS FUNCTION RETURNS 0 IF THE PID IS VALID. IT ALSO RETURNS THE
// PROCESS CPU TIME IN JIFFIES AND MAJOR AND MINOR PAGE FAULT COUNTS
// SINCE THE LAST INVOCATION OF THE FUNCTION FOR THE SPECIFIED PID.
// OTHERWISE IT RETURNS -1
int get_cpu_use(int pid, unsigned long *min_flt, unsigned long *maj_flt,
         unsigned long *utime, unsigned long *stime)
{
        int ret = -1;
        struct task_struct* task;
        rcu_read_lock();
        task=find_task_by_pid(pid);
        if (task!=NULL) {
                *min_flt=task->min_flt;
                *maj_flt=task->maj_flt;
                *utime=task->utime;
                *stime=task->stime;

                task->maj_flt = 0;
                task->min_flt = 0;
                task->utime = 0;
                task->stime = 0;
                ret = 0;
        }
        rcu_read_unlock();
        return ret;
}

#endif
