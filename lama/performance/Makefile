TESTS=$(sort $(basename $(wildcard *.lama)))

LAMAC=lamac
LAMA_INTERPRETER=../../src/lama_interpreter

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo $@

	@echo "Run lama with -i"
	LAMA=../runtime echo "42" | `which time` -f "$@\t%U" $(LAMAC) -i $<

	@echo "Run lama with -s"
	LAMA=../runtime echo "42" | `which time` -f "$@\t%U" $(LAMAC) -s $<


	@echo "Compiled binary with lama"
	LAMA=../runtime $(LAMAC)  $< && `which time` -f "$@\t%U" ./$@

	$(LAMAC) -b $<
	@echo "Run my interpreter"
	`which time` -f "$@\t%U" $(LAMA_INTERPRETER) $@.bc 

clean:
	$(RM) test*.log *.s *~ $(TESTS) *.i
