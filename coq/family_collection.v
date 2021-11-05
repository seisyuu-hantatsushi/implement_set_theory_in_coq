From mathcomp Require Import ssreflect.

Require Import collect_operator.
Require Import direct_product.
Require Import mapping.
Require Import mapping_space.

(* 族:X_iは添字集合:Iから集合:Xへの写像である. X_i:I->X *)
(* family X_i is alias of mapping indexing set I to set X *)
Definition IndexedFamily {U V:Type} (map:U -> V) (I:Collection U) (X: Collection V) :=
  forall i:U, i ∈ I -> exists Xi:V, Xi = map i /\ Xi ∈ X.

(* 族で添字に対応する要素が集合である場合,集合族と言う. 集合族は関数,写像 *)
(* 添字集合の要素iからと集合の集合より紐付いた集合を取り出す関数 *)
Definition FamilyOfSetsWithFunction {U:Type} (map:U -> Collection U) (I:Collection U) (X: Collection (Collection U)) :=
  IndexedFamily map I X.

Definition TypeOfGraphOfFamilyOfSets U := Collection (TypeOfOrderedPair (Collection U)).

(* 族のGraphは添字集合と集合の直積の部分集合である *)
(* Graph of family is subset of direct product of indexing set I to set X *)
(* 集合族のGraph *)
Inductive GraphOfFamilyOfSets {U:Type} (map: U -> Collection U) (I:Collection U) (X: Collection (Collection U)) :
  TypeOfGraphOfFamilyOfSets U :=
| definition_of_graph_of_family_set:
    forall Z:TypeOfOrderedPair (Collection U),
      (exists i:U, exists x':Collection U, Z=<|{|i|},x'|> /\ x' = map i /\ i ∈ I /\ x' ∈ X) ->
      Z ∈ GraphOfFamilyOfSets map I X.

(* 集合族から添字により集合を得ます *)
Definition PickIndexedSetByFamilySet {U V:Type} (map:V -> Collection U) (i:V) : Collection U := map i.

(* ⌞ Unicode: 231E BOTTOM LEFT CORNER *)
Notation "X_I ⌞ i" := (PickIndexedSetByFamilySet X_I i) (right associativity, at level 20).

(* 部分集合族 *)
Definition FamilySubsetWithIndexingFunction

Inductive BigCupOfFamilySet {U V:Type} (I:Collection V) (X_I: V -> Collection U): Collection U :=
| intro_of_bigcup_of_family: forall x:U, (exists i:V, i ∈ I /\ x ∈ (X_I ⌞ i)) -> x ∈ BigCupOfFamilySet I X_I.

Notation "⋃{ I , X_I }" := (BigCupOfFamilySet I X_I).

Inductive BigCapOfFamilySet {U V:Type} (I:Collection V) (X_I: V -> Collection U) : Collection U :=
| intro_of_bigcap_of_family: forall x: U, (forall i:V, i ∈ I -> x ∈ (X_I ⌞ i)) -> x ∈ BigCapOfFamilySet I X_I.

Notation "⋂{ I , X_I }" := (BigCapOfFamilySet I X_I).

(* 被覆 *)
Definition CoveringByFamilySet {U V:Type} (I:Collection V) (X:Collection U) (X_I:V->Collection U) := X ⊂ ⋃{ I , X_I }.

Section FamilyCollection.
  Variable U:Type.

  (* 添字集合の要素iと集合族の要素は一意に決まる. *)
  Theorem indexed_set_is_unique:
    forall (X_I:U -> Collection U) (I:Collection U) (X': Collection (Collection U)),
      FamilySetWithIndexingFunction X_I I X' ->
      forall (i:U), i ∈ I -> exists! X_i:Collection U, X_I i = X_i.
  Proof.
    move => f_i I X' HF i HiI.
    unfold FamilySetWithIndexingFunction in HF.
    unfold FamilyCollection in HF.
    apply HF in HiI.
    inversion HiI as [X_i].
    inversion H.
    exists X_i.
    split.
    apply sym_eq.
    apply H0.
    move => x' HF'.
    rewrite -HF'.
    trivial.
  Qed.

  (* 添字集合が空なら集合族の合併は空 *)
  Theorem indexed_set_eq_empty_to_bigcup_eq_empty:
    forall  (X_I: U -> Collection U) (I:Collection U),
      I = `Ø` ->
      ⋃{ I , (fun i:U => X_I ⌞ i) } = `Ø`.
  Proof.
    move => X_I I HIE.
    apply mutally_included_to_eq.
    split => x H.
    inversion H as [x0].
    inversion H0 as [i0].
    inversion H2.
    rewrite HIE in H3.
    apply DoubleNegativeElimination.
    move => HxE.
    move: H3.
    apply noone_in_empty.
    apply DoubleNegativeElimination.
    move => HxE.
    move: H.
    apply noone_in_empty.
  Qed.

  (* 添字集合が空なら集合族の交わりは全体集合 *)
  Theorem indexed_set_eq_empty_to_bigcap_eq_full:
    forall (X_I: U -> Collection U) (I:Collection U),
      I = `Ø` ->
      ⋂{ I , (fun i:U => X_I ⌞ i) } = (FullCollection U).
  Proof.
    move => X_I I HIE.
    apply mutally_included_to_eq.
    split => x H.
    apply intro_full_collection.
    split => i HiI.
    apply DoubleNegativeElimination => HXI.
    rewrite HIE in HiI.
    move: HiI.
    apply noone_in_empty.
  Qed.

  (* 添字集合が空なら部分集合族の交わりはもとの集合の全体 *)
  Theorem indexed_subset_eq_empty_to_bigcap_eq_full:
    forall (X_I: U -> Collection U) (I:Collection U) (X:Collection U),
    forall i:U, i ∈ I -> X_I ⌞ i ⊂ X ->
    I = `Ø` ->
    ⋂{ I , (fun i:U => X_I ⌞ i) } = X.
  Proof.
    move => X_I I X i HiI HSX HIE.
    have L1: forall i:U, i ∉ I.
    rewrite HIE.
    apply noone_in_empty.
    apply DoubleNegativeElimination => HnxX.
    apply (L1 i).
    apply HiI.
  Qed.

End FamilyCollection.
