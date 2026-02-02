KERNEL_SRC:= <PATH_TO_YOUR_5.15.127_KERNEL>
SUBDIR= $(PWD)
GCC:=gcc
RM:=rm

.PHONY : clean

all: clean modules app

obj-m:= mp2.o

modules:
	$(MAKE) -C $(KERNEL_SRC) M=$(SUBDIR) modules

app: userapp.c userapp.h
	$(GCC) -o userapp userapp.c

clean:
	$(RM) -f userapp *~ *.ko *.o *.mod.c Module.symvers modules.order
