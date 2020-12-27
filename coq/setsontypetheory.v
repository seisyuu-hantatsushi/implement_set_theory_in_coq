From mathcomp Require Import ssreflect.

Require Import classical_predicate_logic.

(*
        A Collection does not include itself at type theory.
        For the above reason, we can avoid russel's paradox.
 *)
(*
        Collection is aliase of LogicFunction.
 *)
(*
  Uはこの世のすべての記号,元を集めた集合.
  論理関数の判定により,集合を作成する. (分出公理と目的は同じ.).
 *)

Definition Collection U := LogicFunction U.

Definition In (U:Type) (X:Collection U) (x:U) : Prop := X x.

Notation "x ∈ X" := (In _ X x) (right associativity, at level 30) : type_scope.
Notation "x ∉ X" := (~(In _ X x)) (right associativity, at level 30) : type_scope.

(* 内包の公理 *)
Theorem AxiomOfComprehension:
  forall U:Type, forall F:LogicFunction U, exists z':Collection U, forall a:U, a ∈ z' <-> F a.
Proof.
  move => U F.
  exists F.
  move => a.
  rewrite /iff. split => H; apply H.
Qed.

(* 外延性公理 *)
Axiom AxiomOfExtentionality:
  forall U:Type, forall {x' y':Collection U},
      (forall x:U, (x ∈ x' <-> x ∈ y')) -> x' = y'.

Theorem collection_is_unique_existence:
  forall U:Type, forall F:LogicFunction U, exists! y':Collection U, forall x:U, (x ∈ y') <-> F x.
Proof.
  move => U F.
  exists F.
  rewrite /unique.
  split. move => x.
  rewrite /iff. split => H; apply H.
  move => x' H.
  apply AxiomOfExtentionality.
  move => x.
  apply: iff_sym.
  apply: (H x).
Qed.

Section Examples.
  Inductive DayOfTheWeek : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

  Definition Weekdays : Collection DayOfTheWeek :=
    fun d => d = monday \/ d = tuesday \/ d = wednesday \/ d = thursday \/ d = friday.
  Definition Holidays : Collection DayOfTheWeek :=
    fun d => d = saturday \/ d = sunday.

  Goal monday ∈ Weekdays.
  Proof.
    left.
    reflexivity.
  Qed.

  Goal forall d:DayOfTheWeek, d ∈ Weekdays <-> Weekdays d.
  Proof.
    move => d.
    rewrite /iff. split => H; apply H.
  Qed.

End Examples.

Export classical_predicate_logic.
