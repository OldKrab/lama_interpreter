all: 
	$(MAKE) -C src

tests:
	$(MAKE) -C lama/regression
	$(MAKE) -C lama/regression/expressions
	$(MAKE) -C lama/regression/deep-expressions

clean:
	$(MAKE) -C src clean
	$(MAKE) -C lama/regression clean
	$(MAKE) -C lama/regression/deep-expressions clean
	$(MAKE) -C lama/regression/expressions clean