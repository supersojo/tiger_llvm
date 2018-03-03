TARGET = main
SRCS = $(filter-out runtime.c,$(wildcard *.c))
OBJS = $(SRCS:.c=.o)
DEPS = $(SRCS:.c=.d)

.PHONY: all deps clean

all: deps $(TARGET)
tiger:
	@./main
	@gcc -c tiger.S -o tiger.o
	@gcc -c runtime.c -o runtime.o
	@gcc tiger.o runtime.o -o tiger

$(TARGET): $(DEPS) $(OBJS) $(SRCS)
	@g++ $(OBJS) -o $@
	@echo linking $(TARGET) 

deps: $(DEPS)

%.d: %.c
	@g++ -MM $< > $@

%.o: %.c
	@g++ -c -g -Wno-write-strings $< -o $@
	@echo compiling $<

-include $(DEPS)

clean:
	rm -f main
	rm -f tiger
	rm -f *.d
	rm -f *.o
	rm -f *.S
