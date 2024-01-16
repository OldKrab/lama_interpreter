CC=gcc
CFLAGS ?= -m32 -g2 -fstack-protector-all

TARGET = lama_interpreter

all: $(TARGET)

clean:
	$(MAKE) -C lama/runtime clean
	rm -rf *.o $(TARGET)

$(TARGET): main.o lama_runtime
	$(CC) $(CFLAGS) main.o lama/runtime/runtime.a -o $(TARGET)

%.o: %.c
	$(CC) $(CFLAGS) -c $*.c


lama_runtime: 
	$(MAKE) -C lama/runtime

