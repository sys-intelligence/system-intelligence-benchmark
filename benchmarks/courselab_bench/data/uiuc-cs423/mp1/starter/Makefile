obj-m += mp1.o

all:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules
	gcc -o userapp userapp.c

clean:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean
	$(RM) userapp
