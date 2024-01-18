.PHONY: src tests clean performance

all: src tests performance
	
tests: src
	$(MAKE) -C lama/regression
	$(MAKE) -C lama/regression/expressions
	$(MAKE) -C lama/regression/deep-expressions

performance: src
	$(MAKE) -C lama/performance

src:
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean
	$(MAKE) -C lama/regression clean
	$(MAKE) -C lama/regression/deep-expressions clean
	$(MAKE) -C lama/regression/expressions clean
	$(MAKE) -C lama/performance clean
