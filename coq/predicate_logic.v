From mathcomp Require Import ssreflect.

Section PredicateLogic.

  Definition LogicFunction I := I -> Prop.
  Definition RelationLogicFunction X Y := X -> Y -> Prop.

  (* 自同律 *)
  Theorem LawOfIdentity: forall A:Prop, A <-> A.
  Proof.
    rewrite /iff. split. apply. apply.
  Qed.

  Theorem NotFalse : ~False.
  Proof.
    apply.
  Qed.

  (* 矛盾律 *)
  Theorem LawOfContradiction: forall P:Prop, P /\ ~P <-> False.
  Proof.
    rewrite /iff.
    split.
    case => H0.
    apply.
    apply H0.
    case.
  Qed.

  (* 二重否定 *)
  (*
   クジラは哺乳類である(A)の命題の否定は,クジラは哺乳類でない(not A).
   クジラは哺乳類である(A)の命題の二重否定は,クジラは哺乳類でないことはない.
   クジラは哺乳類でないことはない(not not A)から否定を一つ外すと,
   クジラは哺乳類でない,これはクジラが哺乳類以外のなにかであるなので,
   これに否定をつけても,クジラが哺乳類であることを保証しないので,
   二重否定の除去を認めない,構成的論理では~~A -> Aが成立しない.
   *)
  Theorem DoubleNegative: forall A:Prop, A -> ~~A.
  Proof.
    rewrite /not.
    move => A HA HNA.
    apply HNA.
    apply HA.
  Qed.

  (* 冪等律 *)
  Theorem LawOfIdempotenceAtAnd: forall P:Prop, P /\ P <-> P.
  Proof.
    move => P.
    rewrite /iff.
    split.
    case.
    move => HP.
    apply.
    move => HP.
    split.
    apply HP.
    apply HP.
  Qed.

  Theorem LawOfIdempotenceAtOr: forall P:Prop, P \/ P <-> P.
  Proof.
    move => P.
    rewrite /iff.
    split.
    case.
    apply.
    apply.
    move => HP.
    right.
    apply HP.
  Qed.

  (* 交換律 *)
  Theorem LawOfCommutativeAtAnd: forall A B:Prop, A /\ B <-> B /\ A.
  Proof.
    move => A B.
    rewrite /iff.
    split; case; move => H0 H1; split.
    apply H1.
    apply H0.
    apply H1.
    apply H0.
  Qed.

  (* 交換律 *)
  Theorem LawOfCommutativeAtOr: forall A B:Prop, A \/ B <-> B \/ A.
  Proof.
    move => A B.
    rewrite /iff.
    split; case; move => H.
    right.
    apply H.
    left.
    apply H.
    right.
    apply H.
    left.
    apply H.
  Qed.

  (* 結合律 *)
  Theorem LawOfAssociateAtAnd: forall A B C:Prop, (A /\ B) /\ C <-> A /\ (B /\ C).
  Proof.
    move => A B C.
    rewrite /iff.
    split; case.
    case.
    move => HA HB HC.
    split.
    apply HA.
    split.
    apply HB.
    apply HC.
    move => HA.
    case.
    move => HB HC.
    split.
    split.
    apply HA.
    apply HB.
    apply HC.
  Qed.

  (* 結合律 *)
  Theorem LawOfAssociateAtOr: forall A B C:Prop, (A \/ B) \/ C <-> A \/ (B \/ C).
  Proof.
    move => A B C.
    rewrite /iff.
    split; case.
    case; move => H.
    left.
    apply H.
    right.
    left.
    apply H.
    move => H.
    right.
    right.
    apply H.
    move => H.
    left.
    left.
    apply H.
    case; move => H.
    left.
    right.
    apply H.
    right.
    apply H.
  Qed.

  (* 分配律 *)
  Theorem LawOfDistributiveByOr: forall A B C:Prop, (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
  Proof.
    move => A B C.
    rewrite /iff.
    split.
    case.
    case.
    move => HA HB.
    split; left.
    apply HA.
    apply HB.
    move => HC.
    split; right; apply HC.
    case; move => H0 H1.
    case H0; move => H2.
    case H1; move => H3.
    left.
    split.
    apply H2.
    apply H3.
    right.
    apply H3.
    right.
    apply H2.
  Qed.

  (* 分配律 *)
  Theorem LawOfDistributiveByAnd: forall A B C:Prop, (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
  Proof.
    move => A B C.
    rewrite /iff.
    split; case; case; move => H0 H1.
    left.
    split.
    apply H0.
    apply H1.
    right.
    split.
    apply H0.
    apply H1.
    split.
    left.
    apply H0.
    apply H1.
    split.
    right.
    apply H0.
    apply H1.
  Qed.

  (* 吸収律 *)
  Theorem LawOfAbsorptionToOr: forall A B:Prop, (A /\ B) \/ A <-> A.
  Proof.
    move => A B.
    rewrite /iff.
    split.
    case.
    case.
    move => HA HB.
    apply HA.
    apply.
    move => HA.
    right.
    apply HA.
  Qed.

  (* 吸収律 *)
  Theorem LawOfAbsorptionToAnd: forall A B:Prop, (A \/ B) /\ A <-> A.
  Proof.
    move => A B.
    rewrite /iff.
    split.
    case.
    move => H0.
    apply.
    move => H0.
    split.
    left.
    apply H0.
    apply H0.
  Qed.

  Theorem P_implies_notQ_to_Q_implies_notP:
    forall P Q:Prop, (P -> ~Q) -> (Q -> ~P).
  Proof.
    move => P Q H0 HQ HP.
    apply: H0.
    apply: HP.
    apply: HQ.
  Qed.

  (* 構成的論理(直観主義論理)における対偶 *)
  (* If A implies B, then not B implies not A. *)
  (* 二重否定の除去を認めないので, ここでは逆は成立しない. *)
  Theorem ContrapositionInConstrutiveLogic: forall A B:Prop, (A -> B) -> (~B -> ~A).
  Proof.
    move => A B H0 H1 H2.
    apply H1.
    apply H0.
    apply H2.
  Qed.

  (* If not P or Q are true, then P implies Q. *)
  (* 構成的論理では逆は成り立たない. *)
  Theorem notOr_to_imply:
    forall P Q:Prop, (~P \/ Q) -> (P -> Q).
  Proof.
    move => P Q.
    case; move => H0 H1.
    move: H0.
    case.
    apply H1.
    apply H0.
  Qed.

  (* ド・モルガンの法則, 論理和の否定 *)
  Theorem LawOfDeMorgan_NegtationOfDisjunction:
    forall A B:Prop, ~(A \/ B) <-> (~A /\ ~B).
  Proof.
    move => A B.
    rewrite /iff.
    split.
    move => H0.
    split; move => H1; apply H0.
    left.
    apply H1.
    right.
    apply H1.
    case.
    move => HA HB.
    case.
    apply HA.
    apply HB.
  Qed.

  (* ド・モルガンの法則, 論理積の否定 *)
  (* カッコを開く方は,構成的論理では証明できない *)
  Theorem LawOfDeMorgan_NegtationOfConjunction_Close:
    forall A B:Prop, (~A \/ ~B) -> ~(A /\ B).
  Proof.
    move => A B H0.
    case.
    move => HA HB.
    move: H0.
    case; apply.
    apply HA.
    apply HB.
  Qed.

  Theorem LawOfDeMorgan_NegtationOfConjucation_Open_Weak:
    forall A B:Prop, (A \/ ~B) -> (~(A /\ B) -> (~A \/ ~B)).
  Proof.
    move => A B.
    case; move => H0 H1.
    right.
    move => H2.
    apply H1.
    split.
    apply: H0.
    apply: H2.
    right.
    apply H0.
  Qed.

  Theorem notAnd_to_imply: forall P Q:Prop, ~(P /\ Q) -> (P -> ~Q).
  Proof.
    move => P Q HF HP HQ.
    apply: HF.
    split.
    apply HP.
    apply HQ.
  Qed.

  Theorem imply_to_notAnd: forall P Q:Prop, (P -> ~Q) -> ~(P /\ Q).
  Proof.
    move => P Q H0.
    case.
    move => HP HQ.
    apply: H0.
    apply: HP.
    apply: HQ.
  Qed.

  Theorem imply_iff_notAnd: forall P Q:Prop, (P -> ~Q) <-> ~(P /\ Q).
  Proof.
    move => P Q.
    rewrite /iff.
    split.
    apply: imply_to_notAnd.
    apply: notAnd_to_imply.
  Qed.

  Theorem and_imply_and_to_dist:
    forall P Q R S:Prop, (P /\ Q -> R /\ S) -> (P /\ Q -> R) /\ (P /\ Q -> S).
  Proof.
    move => P Q R S H.
    split; apply H.
  Qed.

  Theorem and_imply_and_dist_to:
    forall P Q R S:Prop, (P /\ Q -> R) /\ (P /\ Q -> S) -> (P /\ Q -> R /\ S).
  Proof.
    move => P Q R S.
    case => H0 H1 H.
    split; [apply H0|apply H1]; by [].
  Qed.

  Theorem and_imply_and_dist:
    forall P Q R S:Prop, (P /\ Q -> R /\ S) <-> (P /\ Q -> R) /\ (P /\ Q -> S).
  Proof.
    move => P Q R S.
    rewrite /iff. split.
    apply and_imply_and_to_dist.
    apply and_imply_and_dist_to.
  Qed.

  Theorem DoubleNegativeLawOfExcludeMiddle: forall P:Prop, ~~(P \/ ~P).
  Proof.
    move => P H.
    apply H.
    right.
    move => H0.
    apply H.
    left.
    apply H0.
  Qed.

  Theorem ForallToFree: forall I:Type, forall t:I, forall P:LogicFunction I, (forall x:I, P x) -> P t.
  Proof.
    move => I t P H.
    apply H.
  Qed.

  Theorem FreeToBind: forall I:Type, forall t:I, forall P:LogicFunction I, P t -> (exists x, P x).
  Proof.
    move => I t P H.
    exists t. apply: H.
  Qed.

  Theorem SwapForall: forall I:Type, forall P:LogicFunction I, (forall x:I, P x) -> (forall y:I, P y).
  Proof.
    move => I P H y. apply H.
  Qed.

  Theorem SwapExists: forall I:Type, forall P:LogicFunction I, (exists x:I, P x) -> (exists y:I, P y).
  Proof.
    move => I P.
    case => x HP.
    exists x. apply HP.
  Qed.

  Theorem DeMorganNotExists: forall I:Type, forall P:LogicFunction I, ~(exists x:I, P x) <-> forall x:I, ~(P x).
  Proof.
    move => I P.
    rewrite /iff. split; move => H.
    move => x H0.
    apply H.
    exists x.
    apply H0.
    case.
    apply H.
  Qed.

  Theorem DeMorganNotForall_Close: forall I:Type, forall P:LogicFunction I, (exists x:I, ~ (P x)) -> ~(forall x:I, P x).
  Proof.
    move => I P.
    case => x H HN.
    apply /H /HN.
  Qed.

  Theorem DeMorganNotExistsNot: forall I:Type, forall P:LogicFunction I, ~(exists x:I, ~ (P x)) <-> (forall x:I, ~~P x).
  Proof.
    move => I P.
    apply: DeMorganNotExists.
  Qed.

  Theorem forall_bound_and_out:
    forall I:Type, forall (A B:LogicFunction I),
        (forall x:I, A x) /\ (forall y:I, B y) -> forall x y:I, A x /\ B y.
  Proof.
    move => I A B.
    case => H0 H1 x y.
    split; by [].
  Qed.

  Theorem forall_bound_and_in:
    forall I:Type, forall (A B:LogicFunction I),
        (forall x y:I, A x /\ B y) -> (forall x:I, A x) /\ (forall y:I, B y).
  Proof.
    move => I A B H.
    split => x; apply H; by [].
  Qed.

  Theorem forall_bound_and_in_out:
      forall I:Type, forall (A B:LogicFunction I),
          (forall x:I, A x) /\ (forall y:I, B y) <-> forall x y:I, A x /\ B y.
  Proof.
    move => I A B.
    rewrite /iff. split.
    apply forall_bound_and_out.
    apply forall_bound_and_in.
  Qed.

  Theorem forall_bound_or_out:
    forall I:Type, forall (A B:LogicFunction I),
        (forall x:I, A x) \/ (forall y:I, B y) -> forall x y:I, A x \/ B y.
  Proof.
    move => I A B.
    case => H x y; [left|right]; by[].
  Qed.

  Theorem exists_bound_and_out:
    forall I:Type, forall (A B:LogicFunction I),
        (exists x:I, A x) /\ (exists y:I, B y) -> exists x y:I, A x /\ B y.
  Proof.
    move => I A B.
    case => [[x HA [y HB]]].
    exists x. exists y.
    split; by [].
  Qed.

  Theorem exists_bound_and_in:
    forall I:Type, forall (A B:LogicFunction I),
        (exists x y:I, A x /\ B y) -> (exists x:I, A x) /\ (exists y:I, B y).
  Proof.
    move => I A B.
    case => [x [y [HA HB]]].
    split; [exists x|exists y]; by [].
  Qed.

  Theorem exists_bound_and_in_out:
    forall I:Type, forall (A B:LogicFunction I),
        (exists x:I, A x) /\ (exists y:I, B y) <-> exists x y:I, A x /\ B y.
  Proof.
    move => I A B.
    rewrite /iff. split.
    apply exists_bound_and_out.
    apply exists_bound_and_in.
  Qed.

End PredicateLogic.









