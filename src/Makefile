CC=gcc
CFLAGS ?= -m32 -g -O0 -std=gnu11
TARGET = lama_interpreter

.PHONY: clean lama_runtime

all: $(TARGET)

clean:
	$(MAKE) -C ../lama/runtime clean
	rm -rf *.o $(TARGET)

$(TARGET): main.o lama_runtime
	$(CC) $(CFLAGS) main.o ../lama/runtime/runtime.a -o $(TARGET)

%.o: %.c
	$(CC) $(CFLAGS) -c $*.c

lama_runtime: 
	$(MAKE) -C ../lama/runtime

