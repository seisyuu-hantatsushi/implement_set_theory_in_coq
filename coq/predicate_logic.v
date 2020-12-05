From mathcomp Require Import ssreflect.

Module PredicateLogic.

  Section PredicateLogic.

    Theorem LawOfIdentity: forall A:Prop, A <-> A.
    Proof.
      rewrite /iff.
      split.
      apply.
      apply.
    Qed.

    Theorem NotFalse : ~False.
    Proof.
      rewrite /not.
      apply.
    Qed.

    Theorem DoubleNegative: forall A:Prop, A -> ~~A.
    Proof.
      rewrite /not.
      move => A HA HNA.
      apply HNA.
      apply HA.
    Qed.

  End PredicateLogic.

End PredicateLogic.
