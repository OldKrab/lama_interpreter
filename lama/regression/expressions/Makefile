TESTS=$(sort $(basename $(wildcard generated*.lama)))

LAMAC=lamac
LAMA_INTERPRETER=../../../src/lama_interpreter

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo "expresions/$@"
	$(LAMAC) -b $@.lama
	$(LAMA_INTERPRETER) $@.bc < $@.input > $@.log
	diff $@.log orig/$@.log

clean:
	rm -f *.log *.s *~
	find . -maxdepth 1 -type f -not -name '*.*' -not -name 'Makefile' -delete

