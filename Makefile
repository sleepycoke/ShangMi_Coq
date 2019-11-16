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
	rm -f *.glob *.log *.vo 
