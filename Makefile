SOURCES = $(wildcard *.v) 
OBJECTS = $(SOURCES:.v=.vo)
MAPPINGS = -R . CertSM  

all: $(OBJECTS) .depend

-include .depend

.depend: $(SOURCES)
	coqdep $(MAPPINGS) $^ > $@

./%.vo: ./%.v
	coqc -R . CertSM $<

./CCompLib/%.vo: ./CCompLib/%.v
	coqc -Q ./CCompLib CCompLib $<


clean:
	rm -f .depend
	rm -f *.glob *.log *.vo CCompLib/*.glob CCompLib/*.log CCompLib/*.vo 

