SOURCES = $(wildcard *.v) 
OBJECTS = $(SOURCES:.v=.vo)
MAPPINGS = -R . ""  

all: $(OBJECTS) .depend

.depend: $(SOURCES)
	coqdep $(MAPPINGS) $^ > $@

-include .depend

./%.vo: ./%.v
	coqc $(MAPPINGS) $<

.PHONY: clean
clean:
	rm -f .depend
	rm -f *.glob *.log *.vo *.vok *.vos .*.aux
	rm -f Tests/*.glob Tests/*.log Tests/*.vo Tests/*.vok Tests/*.vos Tests/.*.aux

test:
	coqc Tests/ECDef_Test.v
	coqc Tests/Signature_Test.v
	coqc Tests/KeyEx_Test.v
	coqc Tests/Pubkey_Test.v