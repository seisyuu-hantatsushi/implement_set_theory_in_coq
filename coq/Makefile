
all: mapping_morphism.vo sets_of_family.vo

sets_of_family.vo: sets_of_family.v mapping_space.vo mapping.vo
	coqc $<

mapping_space.vo: mapping_space.v collect_operator.vo direct_product.vo mapping.vo
	coqc $<

mapping_morphism.vo: mapping_morphism.v inverse_mapping.vo
	coqc $<

inverse_mapping.vo: inverse_mapping.v mapping.vo
	coqc $<

mapping.vo: mapping.v binary_relation.vo direct_product.vo collect_operator.vo
	coqc $<

binary_relation.vo: binary_relation.v direct_product.vo collect_operator.vo
	coqc $<

direct_product.vo: direct_product.v collect_operator.vo
	coqc $<

collect_operator.vo: collect_operator.v zf.vo
	coqc $<

zf.vo: zf.v relation.vo axiom_of_empty.vo axiom_of_pair.vo axiom_of_union.vo axiom_of_replacement.vo axiom_of_power.vo
	coqc $<

axiom_of_power.vo: axiom_of_power.v relation.vo
	coqc $<

axiom_of_replacement.vo: axiom_of_replacement.v axiom_of_empty.vo axiom_of_pair.vo axiom_of_union.vo relation.vo
	coqc $<

axiom_of_union.vo: axiom_of_union.v axiom_of_pair.vo relation.vo
	coqc $<

axiom_of_pair.vo: axiom_of_pair.v axiom_of_empty.vo relation.vo
	coqc $<

axiom_of_empty.vo: axiom_of_empty.v relation.vo
	coqc $<

relation.vo: relation.v setsontypetheory.vo
	coqc $<

setsontypetheory.vo: setsontypetheory.v classical_predicate_logic.vo
	coqc $<

classical_predicate_logic.vo: classical_predicate_logic.v predicate_logic.vo
	coqc $<

predicate_logic.vo: predicate_logic.v
	coqc $<

clean:
	rm -f *.glob *.vo *.vos *.vok .*.aux
	rm -f *~
