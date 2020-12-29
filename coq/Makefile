
all: zf.vo

zf.vo: relation.vo axiom_of_empty.vo
	coqc zf.v

axiom_of_empty.vo: relation.vo axiom_of_empty.v
	coqc axiom_of_empty.v

relation.vo: setsontypetheory.vo relation.v
	coqc relation.v

setsontypetheory.vo: classical_predicate_logic.vo setsontypetheory.v
	coqc setsontypetheory.v

classical_predicate_logic.vo: predicate_logic.vo classical_predicate_logic.v
	coqc classical_predicate_logic.v

predicate_logic.vo: predicate_logic.v
	coqc predicate_logic.v

clean:
	rm -f *.glob *.vo *.vos *.vok .*.aux
	rm -f *~
