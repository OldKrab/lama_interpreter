.PHONY: src tests clean

all: src tests
	
tests: src
	$(MAKE) -C lama/regression
	$(MAKE) -C lama/regression/expressions
	$(MAKE) -C lama/regression/deep-expressions

src:
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean
	$(MAKE) -C lama/regression clean
	$(MAKE) -C lama/regression/deep-expressions clean
	$(MAKE) -C lama/regression/expressions clean