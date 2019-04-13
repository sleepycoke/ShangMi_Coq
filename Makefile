certsm_make: Tables.v SMS4.v
	coqc -R . CertSM Tables.v; coqc -R . CertSM SMS4.v
clean:
	rm -f *.glob *.log *.vo
