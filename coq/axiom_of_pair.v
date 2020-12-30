From mathcomp Require Import ssreflect.

Require Import relation.
Require Import axiom_of_empty.

(* 対の公理 *)
Axiom AxiomOfPair: forall U:Type, forall {x y:U}, exists z':Collection U, forall z:U, z ∈ z' <-> z = x \/ z = y.

Inductive UnorderedPair (U:Type) (x y:U) : Collection U :=
| unordered_pair_l : x ∈ (UnorderedPair U x y)
| unordered_pair_r : y ∈ (UnorderedPair U x y).

Definition Singleton U x := UnorderedPair U x x.

Notation "{| x ',' y |}" := (UnorderedPair _ x y).
Notation "{| x |}" := (Singleton _ x).

Theorem axiom_of_pair_create_unordered_pair:
  forall {U:Type}, forall {x y:U}, exists z':Collection U, (forall z:U, z ∈ z' <-> z = x \/ z = y) -> {| x , y |} = z'.
Proof.
  move => U x y.
  move: AxiomOfPair => HA.
  move: (HA U x y).
  case => z' HAz.
  exists z' => HAz'.
  apply AxiomOfExtentionality => x0.
  rewrite /iff. split => H0.
  case H0.
  apply HAz.
  left. reflexivity.
  case H0.
  apply HAz.
  right. reflexivity.
  apply HAz.
  right. reflexivity.
  apply HAz in H0.
  case H0 => [ H1 | H1 ]; rewrite H1.
  apply unordered_pair_l.
  apply unordered_pair_r.
Qed.

Theorem unordered_pair_is_satisfied_axiom_of_pair:
  forall {U:Type}, forall {x y:U}, exists z':Collection U, z' = {| x , y |} ->  (forall z:U, z ∈ z' <-> z = x \/ z = y).
Proof.
  move => U x y.
  move: AxiomOfPair => HA.
  move: (HA U x y).
  case => z' HAz.
  exists z' => HE z.
  apply HAz.
Qed.

Theorem singleton_to_eq:
  forall U:Type, forall {x y:U}, x ∈ {| y |} -> x = y.
Proof.
  move => U x y H.
  case H; reflexivity.
Qed.

Theorem eq_to_singleton:
  forall U:Type, forall {x y:U}, x = y -> x ∈ {| y |}.
Proof.
  move => U x y H.
  rewrite H.
  left.
Qed.

Theorem singleton_iff_eq:
  forall U:Type, forall {x y:U}, x ∈ {| y |} <-> x = y.
Proof.
  move => U x y.
  rewrite /iff. split.
  apply singleton_to_eq.
  apply eq_to_singleton.
Qed.

Theorem singleton_eq_to_element_eq:
  forall U:Type, forall {x y:U}, {| x |} = {| y |} -> x = y.
Proof.
  move => U x y H.
  apply singleton_iff_eq.
  rewrite -H.
  apply unordered_pair_r.
Qed.

Theorem element_eq_to_singleton_eq:
  forall U:Type, forall {x y:U}, x = y -> {| x |} = {| y |}.
Proof.
  move => U x y H.
  rewrite H. reflexivity.
Qed.

Theorem singleton_eq_iff_element_eq:
  forall U:Type, forall {x y:U}, {| x |} = {| y |} <-> x = y.
Proof.
  move => U x y.
  rewrite /iff. split.
  apply singleton_eq_to_element_eq.
  apply element_eq_to_singleton_eq.
Qed.

Theorem unordered_pair_is_uniqueness:
  forall {U:Type}, forall {x y:U}, forall z':Collection U, (forall z:U, z ∈ z' <-> z = x \/ z = y) -> {| x , y |} = z'.
Proof.
  move => U x y z' H.
  apply AxiomOfExtentionality => x0.
  rewrite /iff. split.
  case; apply H.
  left. reflexivity.
  right. reflexivity.
  move => H0.
  apply (H x0) in H0.
  case H0 => H1;rewrite H1.
  left.
  right.
Qed.

Theorem unordered_pair_to_or:
  forall {U:Type}, forall {x y:U}, forall z':Collection U, {| x , y |} = z' -> (forall z:U, z ∈ z' <-> z = x \/ z = y).
Proof.
  move => U x y z' H z.
  rewrite -H.
  rewrite /iff. split => H0.
  case H0.
  left. reflexivity.
  right. reflexivity.
  case: H0 => H1; rewrite H1.
  apply unordered_pair_l.
  apply unordered_pair_r.
Qed.

Theorem unordered_pair_is_or:
  forall {U:Type}, forall {x y:U}, forall z':Collection U, (forall z:U, z ∈ z' <-> z = x \/ z = y) <-> {| x , y |} = z'.
Proof.
  move => U x y z'.
  rewrite /iff. split.
  apply unordered_pair_is_uniqueness.
  apply unordered_pair_to_or.
Qed.

Theorem unorderedPair_elements_is_sym:
  forall U:Type, forall {x y:U}, {| x , y |} = {| y , x |}.
Proof.
  move => U x y.
  apply AxiomOfExtentionality => x0.
  rewrite /iff. split; case.
  apply unordered_pair_r. apply unordered_pair_l.
  apply unordered_pair_r. apply unordered_pair_l.
Qed.

Inductive OrderedPair (U:Type) (x y:U) : Collection (Collection U) :=
| ordered_pair_l : In (Collection U) (OrderedPair U x y) (Singleton U x)
| ordered_pair_r : In (Collection U) (OrderedPair U x y) (UnorderedPair U x y).
