include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

BOOKS = ite complete-set generalization gen2 trap poly fuzzm-datatypes poly-proofs doublecheck feature gen3 restriction rat-to-int

fuzzm-datatypes.cert: poly.cert

poly-proofs.cert: fuzzm-datatypes.cert

feature.cert: doublecheck.cert

gen3.cert: feature.cert

trap.cert: generalization.cert

restriction.cert: gen3.cert

poly-proofs.html:
	source-highlight -i poly-proofs.lisp -o poly-proofs.html
