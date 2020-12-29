From mathcomp Require Import ssreflect.

Require Import relation.
Require Import axiom_of_empty.

(* 対の公理 *)
Axiom AxiomOfPair: forall U:Type, forall {x y:U}, exists z':Collection U, forall z:U, z ∈ z' <-> z = x \/ z = y.

Inductive UnorderedPair (U:Type) (x y:U) : Collection U :=
| unordered_pair_l : x ∈ (UnorderedPair U x y)
| unordered_pair_r : y ∈ (UnorderedPair U x y).

Definition Singleton U x := UnorderedPair U x x.

Notation "{ x ',' y }" := (UnorderedPair _ x y) (at level 31).
Notation "{ x , }" := (Singleton _ x).

Theorem axiom_of_pair_create_unordered_pair:
  forall {U:Type}, forall {x y:U}, exists z':Collection U, (forall z:U, z ∈ z' <-> z = x \/ z = y) -> { x , y } = z'.
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
  forall {U:Type}, forall {x y:U}, exists z':Collection U, z' = { x , y } ->  (forall z:U, z ∈ z' <-> z = x \/ z = y).
Proof.
  move => U x y.
  move: AxiomOfPair => HA.
  move: (HA U x y).
  case => z' HAz.
  exists z' => HE z.
  apply HAz.
Qed.

Theorem singleton_to_eq:
  forall U:Type, forall {x y:U}, x ∈ { y , } -> x = y.
Proof.
  move => U x y H.
  case H; reflexivity.
Qed.

Theorem eq_to_singleton:
  forall U:Type, forall {x y:U}, x = y -> x ∈ { y , }.
Proof.
  move => U x y H.
  rewrite H.
  left.
Qed.

Theorem singleton_iff_eq:
  forall U:Type, forall {x y:U}, x ∈ { y , } <-> x = y.
Proof.
  move => U x y.
  rewrite /iff. split.
  apply singleton_to_eq.
  apply eq_to_singleton.
Qed.
