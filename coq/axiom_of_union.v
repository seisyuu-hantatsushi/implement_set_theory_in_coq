From mathcomp Require Import ssreflect.

Require Import relation.
Require Import axiom_of_pair.

Axiom AxiomOfUnion: forall U:Type, forall A:Collection (Collection U), exists B:Collection U, forall x:U, (x ∈ B <-> exists (C:Collection U), (x ∈ C /\ C ∈ A)).

Definition UnionFromAxiom U (A:Collection (Collection U)) : Collection U :=
  fun x =>
    exists B:Collection U, forall x:U, (x ∈ B <-> exists (C:Collection U), (x ∈ C /\ C ∈ A)) -> x ∈ B.

Inductive UnionOfCollection (U:Type) (A B:Collection U): Collection U :=
| union_of_collection_l: forall x:U, x ∈ A -> x ∈ UnionOfCollection U A B
| union_of_collection_r: forall x:U, x ∈ B -> x ∈ UnionOfCollection U A B
where "A ∪ B" := (UnionOfCollection _ A B).

Inductive BigCupOfCollection (U:Type) (X:Collection (Collection U)): Collection U :=
| intro_bigcup_of_collection: forall A: Collection U, forall x:U, x ∈ A /\ A ∈ X -> x ∈ BigCupOfCollection U X
where "⋃ X" := (BigCupOfCollection _ X).

Notation "{| x , y , .. , z |}" :=
  (UnionOfCollection _ .. (UnionOfCollection _ (Singleton _ x) (Singleton _ y)) .. (Singleton _ z)).

Theorem two_element_union_eq_unordered_pair:
  forall U:Type, forall {a b:U}, (| a , b |) = {| a , b |}.
Proof.
  move => U a b.
  apply mutally_included_iff_eq.
  split => x.
  case.
  left. apply singleton_iff_eq. reflexivity.
  right. apply singleton_iff_eq. reflexivity.
  case => x0 H; apply singleton_iff_eq in H; rewrite H.
  left.
  right.
Qed.

Theorem triple_ext_notation_to_or_eq:
  forall U:Type, forall {x a b c:U}, x ∈ {| a , b , c |} -> x = a \/ x = b \/ x = c.
Proof.
  move => U x a b c.
  case => x0.
  case => x1 H; apply singleton_iff_eq in H.
  left. by [].
  right. left. by [].
  move => H.
  apply singleton_iff_eq in H.
  right. right. by [].
Qed.

Theorem triple_or_eq_to_ext_notation:
  forall U:Type, forall {x a b c:U}, x = a \/ x = b \/ x = c -> x ∈ {| a , b , c |}.
Proof.
  move => U x a b c.
  case => H.
  left. left. apply singleton_iff_eq. by [].
  case: H => H0.
  left. right. apply singleton_iff_eq. by [].
  right. apply singleton_iff_eq. by [].
Qed.

Theorem triple_ext_notation_iff_or_eq:
  forall U:Type, forall {x a b c:U}, x ∈ {| a , b , c |} <-> x = a \/ x = b \/ x = c.
Proof.
  move => U x a b c.
  rewrite /iff. split.
  apply triple_ext_notation_to_or_eq.
  apply triple_or_eq_to_ext_notation.
Qed.

Section UnionFromAxiomTest.
  Variable U:Type.
  Variable a b c : U.
  Variable A B C:Collection U.

  Goal forall x:U, x ∈ UnionFromAxiom U (| A , B |) -> exists z':Collection U, z' = A ∪ B -> x ∈ z'.
  Proof.
    move => x.
    case => x' H.
    exists x'.
    move => H0.
    apply H.
    rewrite /iff. split; rewrite H0; case => x0 H1.
    exists A.
    split. by [].
    apply unordered_pair_l.
    exists B.
    split. by [].
    apply unordered_pair_r.
    case: H1 => H1 H2.
    apply in_unorder_pair_to_in_or in H2.
    case: H2 => H3; apply singleton_iff_eq in H3; rewrite H3 in H1.
    left. by [].
    right. by [].
  Qed.

  Goal ⋃ (| A , B |) = A ∪ B.
  Proof.
    apply AxiomOfExtentionality => x.
    rewrite /iff. split.
    +case => A0 x0.
     case => H0 H1.
     apply in_unorder_pair_iff_in_or in H1.
     case: H1 => H1; apply singleton_to_eq in H1; rewrite H1 in H0.
     left. by [].
     right. by [].
    +case => x0 H.
     apply (intro_bigcup_of_collection U (|A,B|) A).
     split. by [].
     left.
     apply (intro_bigcup_of_collection U (|A,B|) B).
     split. by [].
     right.
  Qed.

  Goal ⋃ {| A , B , C |} = A ∪ B ∪ C.
  Proof.
    apply AxiomOfExtentionality => x.
    rewrite /iff. split.
    case => x0' x0.
    case => H0 H1.
    apply triple_ext_notation_to_or_eq in H1.
    case: H1 => H1.
    rewrite H1 in H0.
    left. by [].
    case: H1 => H2; rewrite H2 in H0.
    right. left. by [].
    right. right. by [].
    case => x0 H.
    apply: (((intro_bigcup_of_collection U {| A , B , C |}) A) x0).
    split. by [].
    left. left. apply singleton_iff_eq. reflexivity.
    case: H => x1 H.
    apply: (((intro_bigcup_of_collection U {| A , B , C |}) B) x1).
    split. by [].
    left. right. apply singleton_iff_eq. reflexivity.
    apply: (((intro_bigcup_of_collection U {| A , B , C |}) C) x1).
    split. by [].
    right. apply singleton_iff_eq. reflexivity.
  Qed.

  Goal (| a , b |) ∪ {| c |} = {| a , b , c |}.
  Proof.
    apply mutally_included_iff_eq.
    split => x.
    case => x0.
    case. left.
    left.
    apply singleton_iff_eq. reflexivity.
    left. right.
    apply singleton_iff_eq. reflexivity.
    move => H.
    right. by [].
    case => x0 H.
    left.
    case H => x1 H0; apply singleton_iff_eq in H0; rewrite H0.
    left.
    right.
    right.
    apply H.
  Qed.

End UnionFromAxiomTest.

Theorem union_include_left: forall U:Type, forall {X Y:Collection U}, X ⊂ X ∪ Y.
Proof.
  move => U X Y x H.
  left. by [].
Qed.

Theorem union_include_right: forall U:Type, forall {X Y:Collection U}, Y ⊂ X ∪ Y.
Proof.
  move => U X Y x H.
  right. by [].
Qed.

Theorem in_union_to_in_or:
  forall U:Type, forall t:U, forall {X Y:Collection U}, t ∈ X ∪ Y -> t ∈ X \/ t ∈ Y.
Proof.
  move => U t X Y.
  case => x H.
  left. by [].
  right. by [].
Qed.

Theorem in_or_to_in_union:
  forall U:Type, forall t:U, forall {X Y:Collection U}, t ∈ X \/ t ∈ Y -> t ∈ X ∪ Y.
Proof.
  move => U t X Y.
  case => H.
  left. by [].
  right. by [].
Qed.

Theorem in_union_iff_in_or:
  forall U:Type, forall t:U, forall {X Y:Collection U}, t ∈ X ∪ Y <-> t ∈ X \/ t ∈ Y.
Proof.
  move => U t X Y.
  rewrite /iff. split.
  apply in_union_to_in_or.
  apply in_or_to_in_union.
Qed.

Theorem in_union_to_in_or_three:
  forall U:Type, forall t:U, forall {X Y Z:Collection U}, t ∈ X ∪ Y ∪ Z -> t ∈ X \/ t ∈ Y \/ t ∈ Z.
Proof.
  move => U t X Y Z H.
  apply in_union_iff_in_or in H.
  case: H => H0.
  left. by [].
  apply in_union_iff_in_or in H0.
  right. by [].
Qed.

Theorem in_or_to_in_union_three:
  forall U:Type, forall t:U, forall {X Y Z:Collection U}, t ∈ X \/ t ∈ Y \/ t ∈ Z -> t ∈ X ∪ Y ∪ Z.
Proof.
  move => U t X Y Z H.
  apply in_union_iff_in_or.
  case: H => H1.
  left. by [].
  right. apply in_union_iff_in_or. by [].
Qed.

Theorem LawOfIdempotenceAtUnion:
  forall U:Type, forall {X:Collection U}, X = X ∪ X.
Proof.
  move => U X.
  apply AxiomOfExtentionality => x.
  rewrite /iff. split => H.
  left. by [].
  case: H => x0. exact. exact.
Qed.

Theorem LawOfCommutativeAtUnion:
  forall U:Type, forall {X Y:Collection U}, X ∪ Y = Y ∪ X.
Proof.
  move => U X Y.
  apply AxiomOfExtentionality => x.
  rewrite /iff. split; case => x0 H.
  right. by[].
  left. by[].
  right. by[].
  left. by[].
Qed.

Theorem LawOfAssociateAtUnion:
  forall U:Type, forall {A B C:Collection U}, (A ∪ B) ∪ C = A ∪ (B ∪ C).
Proof.
  move => U A B C.
  apply AxiomOfExtentionality => x.
  rewrite /iff. split; case => x0.
  case => x1 H.
  left. by[].
  right. left. by [].
  move => H.
  right. right. by[].
  move => H.
  left. left. by [].
  case => x1 H.
  left. right. by [].
  right. by [].
Qed.





