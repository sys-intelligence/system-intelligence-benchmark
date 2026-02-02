#define LINUX

#include <linux/module.h>
#include <linux/kernel.h>
#include "mp2_given.h"

// !!!!!!!!!!!!! IMPORTANT !!!!!!!!!!!!!
// Please put your name and email here
MODULE_AUTHOR("Tianyin Xu <tyxu@illinois.edu>");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("CS-423 MP2");

#define DEBUG 1

// mp2_init - Called when module is loaded
int __init mp2_init(void)
{
#ifdef DEBUG
	printk(KERN_ALERT "MP2 MODULE LOADING\n");
#endif
	// Insert your code here ...

	printk(KERN_ALERT "MP2 MODULE LOADED\n");
	return 0;
}

// mp2_exit - Called when module is unloaded
void __exit mp2_exit(void)
{
#ifdef DEBUG
	printk(KERN_ALERT "MP2 MODULE UNLOADING\n");
#endif
	// Insert your code here ...

	printk(KERN_ALERT "MP2 MODULE UNLOADED\n");
}

// Register init and exit funtions
module_init(mp2_init);
module_exit(mp2_exit);
