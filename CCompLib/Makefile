SOURCES = $(wildcard ./*.v)
OBJECTS = $(SOURCES:.v=.vo)
MAPPINGS = -R . CCompLib

.depend: $(SOURCES)
	@echo "Analyzing Coq dependencies"
	coqdep $(MAPPINGS) $^ > .depend

%.vo: %.v .depend
	coqc $(MAPPINGS) $<

all: $(OBJECTS)

-include .depend
clean:
	rm -f *.glob *.log *.vo
