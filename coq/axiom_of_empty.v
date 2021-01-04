From mathcomp Require Import ssreflect.

Require Import relation.

(* Axiom Of Extentionality in setontypetheory *)

Axiom AxiomOfEmpty: forall U:Type, exists z':Collection U, (forall x:U, x ∉ z').

Inductive EmptyCollection (U:Type) : Collection U := .
Inductive FullCollection (U:Type) : Collection U :=
| intro_full_collection: forall x:U, x ∈ FullCollection U.

Notation "`Ø`" :=  (EmptyCollection _) (at level 60).

Definition ComplementOfCollection (U:Type) (X:Collection U) : Collection U :=
  fun x:U => x ∉ X.

Notation "A ^c" := (ComplementOfCollection _ A) (at level 65).

Theorem noone_in_empty:
  forall U:Type, forall x:U, x ∉ `Ø`.
Proof.
  move => U x.
  case.
Qed.

Theorem same_empty_collection_is_exsitance:
  forall U:Type, exists a':Collection U, (forall x:U, x ∉ a') <-> (a' = `Ø`).
Proof.
  move => U.
  case: (AxiomOfEmpty U) => e' HAE.
  exists e'.
  rewrite /iff. split => H.
  apply: AxiomOfExtentionality => x0.
  rewrite /iff. split => H0.
  case: (HAE x0). by [].
  case: (noone_in_empty U x0). by [].
  by [].
Qed.

Theorem noone_in_collection_to_empty_collection:
  forall U:Type, forall {a':Collection U}, (forall x:U, x ∉ a') -> a' = `Ø`.
Proof.
  move => U a' HE.
  apply AxiomOfExtentionality.
  rewrite /iff. split => H.
  case: (HE x). by[].
  case: (noone_in_empty U x). by [].
Qed.

Theorem empty_collection_to_noone_in_collection:
  forall U:Type, forall {a':Collection U}, a' = `Ø` -> (forall x:U, x ∉ a').
Proof.
  move => U a' H.
  rewrite H.
  apply noone_in_empty.
Qed.

Theorem empty_collection_is_noone_in_collection:
  forall U:Type, forall {a':Collection U}, a' = `Ø` <-> (forall x:U, x ∉ a').
Proof.
  move => U a'.
  rewrite /iff. split.
  apply empty_collection_to_noone_in_collection.
  apply noone_in_collection_to_empty_collection.
Qed.

Theorem empty_collection_is_unique:
  forall U:Type, forall {a' b':Collection U}, (forall x: U, x ∉ a') -> (forall x: U, x ∉ b') -> a' = b'.
Proof.
  move => U a' b' HNa HNb.
  apply (noone_in_collection_to_empty_collection U) in HNa.
  apply (noone_in_collection_to_empty_collection U) in HNb.
  rewrite HNa HNb.
  reflexivity.
Qed.

Theorem all_collection_included_empty:
  forall U:Type, forall A:(Collection U), `Ø` ⊂ A.
Proof.
  move => U A x H.
  case: (noone_in_empty U x). by[].
Qed.
