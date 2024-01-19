CC=gcc
CFLAGS = -m32 -g -O2 -std=gnu11 -DNDEBUG
TARGET = lama_interpreter

.PHONY: clean lama_runtime

all: $(TARGET)

clean:
	$(MAKE) -C ../lama/runtime clean
	rm -rf *.o $(TARGET)

$(TARGET): main.o gc_helper.o lama_runtime
	$(CC) $(CFLAGS) main.o gc_helper.o ../lama/runtime/runtime.a -o $(TARGET)

%.o: %.c
	$(CC) $(CFLAGS) -c $*.c

gc_helper.o: gc_helper.s
	$(CC) $(CFLAGS) -c gc_helper.s -o gc_helper.o

lama_runtime: 
	$(MAKE) -C ../lama/runtime

