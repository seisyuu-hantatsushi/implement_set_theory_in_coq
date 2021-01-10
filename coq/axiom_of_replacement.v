From mathcomp Require Import ssreflect.

Require Import relation.
Require Import axiom_of_pair.
Require Import axiom_of_union.

Axiom AxiomOfReplacement:
  forall {U:Type}, forall {R:RelationLogicFunction U U},
      (forall {x y z:U}, ((R x y /\ R x z) -> y = z)) ->
      forall {x': Collection U}, exists y':(Collection U), forall z:U, ( z ∈ y' <-> exists w:U, w ∈ x' /\ R w z ).

Section AxiomOfSeparationFromAxiomOfReplacement.
  Variable U:Type.
  Variable F: LogicFunction U.
  Definition P: RelationLogicFunction U U := fun x y => F x /\ x = y.

  Lemma PisUniuqe: forall {x y z:U}, P x y /\ P x z -> y = z.
  Proof.
    move => x y z.
    case => HP1 HP2.
    have L1: forall x y z : U, y = x /\ z = x -> y = z.
    move => x1 y1 z1.
    case => H0 H1.
    rewrite H0 H1.
    reflexivity.
    apply (L1 x y z).
    suff: x = y /\ x = z.
    case => H0 H1.
    split.
    rewrite H0. reflexivity.
    rewrite H1. reflexivity.
    suff: (F x /\ x = y) /\ (F x /\ x = z).
    case => H0 H1.
    split.
    case H0 => H2 H3. by [].
    case H1 => H2 H3. by [].
    split.
    apply HP1.
    apply HP2.
  Qed.

  Theorem IntroAxiomOfSparation:
    (forall {x': Collection U}, exists y':(Collection U), forall z:U,
          ( z ∈ y' <-> exists w:U, w ∈ x' /\ P w z )) ->
    (forall {x': Collection U}, exists y':(Collection U), forall z:U,
            ( z ∈ y' <-> z ∈ x' /\ F z )).
  Proof.
    have L1: forall x': Collection U, forall y:U, (exists x:U, ( x ∈ x' /\ P x y )) <->
                                                    y ∈ x' /\ F y.
    move => x' y.
    rewrite /iff. split.
    case => x.
    case => Hx.
    case => HFx Hxy.
    split; rewrite -Hxy. by []. by [].
    case => Hyx HFy.
    exists y.
    split.
    apply Hyx.
    split. by[]. reflexivity.
    move => HAF.
    move => x'.
    move: (L1 x') => L1x'.
    move: (HAF x') => HAFx'.
    case HAFx'.
    move => w' HAF0.
    exists w' => z.
    move: (HAF0 z) => HAF0z.
    move: (L1x' z) => L1x'z.
    split.
    move => H.
    apply L1x'z.
    apply HAF0z. by [].
    case => H0 H1.
    apply HAF0z.
    apply L1x'z.
    split; by [].
  Qed.

End AxiomOfSeparationFromAxiomOfReplacement.

Inductive CollectionSparation (U:Type) (F:LogicFunction U) : Collection U :=
| intro_collection_sparation: forall x:U, F x -> x ∈ CollectionSparation U F.

Notation "{| : U | F |}" := (CollectionSparation U F).

Inductive IntersectionOfCollection (U:Type) (A B:Collection U): Collection U :=
| intro_intersection_of_collection: forall x:U, x ∈ A -> x ∈ B -> x ∈ IntersectionOfCollection U A B
where "A ∩ B" := (IntersectionOfCollection _ A B).

Inductive BigCapOfCollection (U:Type) (A': Collection (Collection U)): Collection U :=
| intro_bigcap_of_collection: forall x:U, (forall X:Collection U, X ∈ A' -> x ∈ X) -> x ∈ BigCapOfCollection U A'
where  "⋂ X" := (BigCapOfCollection _ X).

Theorem two_element_intersetion_to_and_in:
  forall U:Type, forall x:U, forall {A B:Collection U}, x ∈ A ∩ B -> x ∈ A /\ x ∈ B.
Proof.
  move => U x A B.
  case => x0 HA HB.
  split. by []. by [].
Qed.

Theorem two_element_and_in_to_intersetion:
    forall U:Type, forall x:U, forall {A B:Collection U}, x ∈ A /\ x ∈ B -> x ∈ A ∩ B.
Proof.
  move => U x A B.
  case => HA HB.
  split. by []. by [].
Qed.

Theorem two_element_intersetion_iff_and_in:
  forall U:Type, forall x:U, forall {A B:Collection U}, x ∈ A ∩ B <-> x ∈ A /\ x ∈ B.
Proof.
  move => U x A B.
  rewrite /iff. split.
  apply two_element_intersetion_to_and_in.
  apply two_element_and_in_to_intersetion.
Qed.

Theorem triple_and_in_to_element_intersetion:
  forall U:Type, forall x:U, forall {A B C:Collection U}, x ∈ A /\ x ∈ B /\ x ∈ C -> x ∈ A ∩ B ∩ C.
Proof.
  move => U x A B C.
  case => HA HBC.
  split. by [].
  apply two_element_and_in_to_intersetion.
  by [].
Qed.

Theorem triple_element_intersetion_to_and_in:
  forall U:Type, forall x:U, forall {A B C:Collection U}, x ∈ A ∩ B ∩ C -> x ∈ A /\ x ∈ B /\ x ∈ C.
Proof.
  move => U x A B C.
  case => x0 HA HBC.
  split. by [].
  apply two_element_intersetion_iff_and_in in HBC. by [].
Qed.

Section IntersectionTest.
  Variable U:Type.
  Variable A B C:Collection U.
  Definition AndFunc A B := fun x:U => x ∈ A /\ x ∈ B.

  Goal {| : U | (AndFunc A B) |} = A ∩ B.
  Proof.
    apply mutally_included_iff_eq.
    split => x; case => x0.
    case => H0 H1.
    split.
    apply H0.
    apply H1.
    move => H0 H1.
    split.
    split.
      by []. by [].
  Qed.

  Goal ⋂ (| A , B |) = A ∩ B.
  Proof.
    apply mutally_included_iff_eq.
    split => x; case => x0.
    move => H.
    move: (H A) (H B) => HA HB.
    split.
    apply HA. left.
    apply HB. right.
    move => HA HB.
    apply: (intro_bigcap_of_collection U (|A , B|)) => X.
    case. by[]. by [].
  Qed.

  Goal ⋂ {| A, B, C |} = A ∩ B ∩ C.
  Proof.
    apply mutally_included_iff_eq.
    split => x.
    case => x0 H.
    split.
    apply H. left. left. apply singleton_iff_eq. reflexivity.
    split; apply H.
    left. right. apply singleton_iff_eq. reflexivity.
    right. apply singleton_iff_eq. reflexivity.
    case => x0 HA HBC.
    split => X HABC.
    apply triple_ext_notation_iff_or_eq in HABC.
    case HABC => HAeq.
    rewrite HAeq. by [].
    apply two_element_intersetion_iff_and_in in HBC.
    case: HBC => HB HC.
    case: HAeq => H; rewrite H; by [].
  Qed.
End IntersectionTest.


