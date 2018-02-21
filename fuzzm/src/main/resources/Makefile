
SOLVER ?= smtinterpol

%.xml: %.lus
	jkind -solver $(SOLVER) -timeout 300 -no_slicing -xml_to_stdout $< > $@

%.vector: %.xml %.inputs
	sed -i '/^Warning/d' $*.xml
	xml2vector.py $*
	test -s $*.vector

%.png:  %.csv
	hist.py $<
	cp $@ ../$@

clean:
	$(RM) -rf *.xml *.vector *.funs

