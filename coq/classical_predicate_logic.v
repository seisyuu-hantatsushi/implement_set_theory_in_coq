From mathcomp Require Import ssreflect.

Require Import  predicate_logic.

Axiom DoubleNegativeElimination: forall A:Prop, ~~A -> A.

(* 対偶 *)
Theorem ContrapositionInClassic: forall P Q: Prop, (~Q -> ~P) -> (P -> Q).
Proof.
  move => P Q H0.
  apply: DoubleNegativeElimination.
  move => H1.
  apply: H0.
  move => H2.
  apply H1.
  move => H3.
  apply H2.
  apply: DoubleNegativeElimination.
  move => H2.
  apply H1.
  move => H3.
  move: H2.
  case.
  apply H3.
Qed.

(* 対偶 *)
Theorem Contraposition: forall P Q: Prop, (P -> Q) <-> (~Q -> ~P).
Proof.
  rewrite /iff. split.
  apply ContrapositionInConstrutiveLogic.
  apply ContrapositionInClassic.
Qed.

Theorem LawOfExcludedMiddle: forall P:Prop, P \/ ~P.
Proof.
  move => P.
  apply DoubleNegativeElimination.
  apply DoubleNegativeLawOfExcludeMiddle.
Qed.

(* If P implies Q, then not P or Q are true *)
Theorem imply_to_notOr:
  forall P Q:Prop, (P -> Q) -> (~P \/ Q).
Proof.
  move => P Q H0.
  move: (LawOfExcludedMiddle P).
  case.
  move => H1.
  right.
  apply H0.
  apply H1.
  move => H1.
  left.
  apply H1.
Qed.

Theorem imply_iff_notOr:
  forall P Q:Prop, (~P \/ Q) <-> (P -> Q).
Proof.
  rewrite /iff.
  split.
  apply: notOr_to_imply.
  apply: imply_to_notOr.
Qed.

Theorem not_imply_to_or:
  forall P Q:Prop, (~P -> Q) -> (P \/ Q).
Proof.
  move => P Q H.
  apply DoubleNegativeElimination.
  move => HF.
  apply LawOfDeMorgan_NegtationOfDisjunction in HF.
  inversion HF as [HF0 HF1].
  apply HF1.
  apply H.
  apply HF0.
Qed.

Theorem PeircesLaw: forall P Q:Prop, ((P -> Q) -> P) -> P.
Proof.
  move => P Q H0.
  apply DoubleNegativeElimination.
  move => H1.
  have: (P -> Q) -> P.
  move => H2.
  move: H1.
  case.
  apply H0.
  apply H2.
  move => H2.
  apply H1.
  apply H0.
  move => H3.
  move: H1.
  case.
  apply H3.
Qed.

Theorem LawOfDeMorgan_NegtationOfConjunction_Open:
  forall A B:Prop,  ~(A /\ B) -> (~A \/ ~B).
Proof.
  move => A B H.
  apply: DoubleNegativeElimination.
  move => H0.
  apply LawOfDeMorgan_NegtationOfDisjunction in H0.
  case: H0 => HNA HNB.
  apply: H.
  split.
  move: HNA.
  apply: DoubleNegativeElimination.
  move: HNB.
  apply: DoubleNegativeElimination.
Qed.

Theorem LawOfDeMorgan_NegtationOfConjunction:
  forall A B:Prop,  (~A \/ ~B) <-> ~(A /\ B).
Proof.
  move => A B.
  rewrite /iff. split.
  apply: LawOfDeMorgan_NegtationOfConjunction_Close.
  apply: LawOfDeMorgan_NegtationOfConjunction_Open.
Qed.

Theorem DeMorganNotForall_Open:
  forall I:Type, forall P:LogicFunction I, ~(forall x:I, P x) -> (exists x:I, ~(P x)).
Proof.
  move => I P.
  apply: ContrapositionInClassic.
  move => H0.
  apply: DoubleNegative.
  move => x.
  apply: DoubleNegativeElimination.
  apply DeMorganNotExistsNot.
  apply: H0.
Qed.

Theorem DeMorganNotForall:
  forall I:Type, forall P:LogicFunction I, ~(forall x:I, P x) <-> (exists x:I, ~(P x)).
Proof.
  rewrite /iff. split.
  apply: DeMorganNotForall_Open.
  apply: DeMorganNotForall_Close.
Qed.

Theorem DeMorganNotForallNot_Open:
  forall I:Type, forall P:LogicFunction I, ~(forall x:I, ~P x) -> (exists x:I, P x).
Proof.
  move => I P H.
  suff: exists x:I, ~~(P x).
  case => [x HNN].
  apply DoubleNegativeElimination in HNN.
  exists x. by [].
  apply: (DeMorganNotForall_Open I (fun x => ~ P x)). by [].
Qed.

Theorem forall_bound_or_in:
  forall I:Type, forall (A B:LogicFunction I),
      (forall x y:I, A x \/ B y) -> (forall x:I, A x) \/ (forall y:I, B y).
Proof.
  move => I A B H.
  apply not_imply_to_or => H0.
  apply DeMorganNotForall_Open in H0.
  case H0 => x HA y.
  move: (H x y) => Hxy.
  apply DoubleNegativeElimination.
  move => H1.
  apply DoubleNegative in Hxy.
  apply Hxy.
  apply LawOfDeMorgan_NegtationOfDisjunction.
  split; by [].
Qed.

Theorem forall_bound_or_in_out:
  forall I:Type, forall (A B:LogicFunction I),
      (forall x y:I, A x \/ B y) <-> (forall x:I, A x) \/ (forall y:I, B y).
Proof.
  move => I A B.
  rewrite /iff. split.
  apply forall_bound_or_in.
  apply forall_bound_or_out.
Qed.

Require Export predicate_logic.
