SOURCES = $(wildcard *.v) $(wildcard CCompLib/*.v)
OBJECTS = $(SOURCES:.v=.vo)
MAPPINGS = -R . CertSM -R ./CCompLib CCompLib

all: $(OBJECTS)

.depend: $(SOURCES)
	coqdep $(MAPPINGS) $^ > $@

./%.vo: ./%.v
	coqc -R . CertSM $<

./CCompLib/%.vo: ./CCompLib/%.v
	coqc -Q ./CCompLib CCompLib $<

-include .depend

clean:
	rm -f .depend
	rm -f *.glob *.log *.vo CCompLib/*.glob CCompLib/*.log CCompLib/*.vo 


