From mathcomp Require Import ssreflect.

Require Import relation.
Require Import axiom_of_empty.

(* 対の公理 *)
Axiom AxiomOfPair: forall U:Type, forall {x y:U}, exists z':Collection U, forall z:U, z ∈ z' <-> z = x \/ z = y.

Inductive UnorderedPair (U:Type) (x y:U) : Collection U :=
| unordered_pair_l : x ∈ (UnorderedPair U x y)
| unordered_pair_r : y ∈ (UnorderedPair U x y).

Definition Singleton U x := UnorderedPair U x x.

Notation "{| x |}" := (Singleton _ x).
Notation "(| x ',' y |)" := (UnorderedPair _ x y).

Theorem axiom_of_pair_create_unordered_pair:
  forall {U:Type}, forall {x y:U}, exists z':Collection U,
        (forall z:U, z ∈ z' <-> z = x \/ z = y) -> (| x , y |) = z'.
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
  forall {U:Type}, forall {x y:U}, exists z':Collection U, z' = (| x , y |) ->  (forall z:U, z ∈ z' <-> z = x \/ z = y).
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

Theorem in_to_singleton_included:
  forall U:Type, forall {x:U}, forall {x':Collection U}, x ∈ x' -> {| x |} ⊂ x'.
Proof.
  move => U x x' H x0.
  case. by []. by [].
Qed.

Theorem singleton_included_to_in:
  forall U:Type, forall {x:U}, forall {x':Collection U}, {| x |} ⊂ x' -> x ∈ x'.
Proof.
  move => U x x'.
  apply.
  apply singleton_iff_eq. reflexivity.
Qed.

Theorem in_iff_singleton_included:
  forall U:Type, forall {x:U}, forall {x':Collection U}, x ∈ x' <-> {| x |} ⊂ x'.
Proof.
  move => U x x'.
  rewrite /iff. split.
  apply: in_to_singleton_included.
  apply: singleton_included_to_in.
Qed.

Theorem unordered_pair_is_uniqueness:
  forall {U:Type}, forall {x y:U}, forall z':Collection U, (forall z:U, z ∈ z' <-> z = x \/ z = y) -> (| x , y |) = z'.
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

Theorem in_unorder_pair_to_in_or:
  forall {U:Type}, forall {x y z:U}, z ∈ (| x , y |) -> z ∈ {| x |} \/ z ∈ {| y |}.
Proof.
  move => U x y z H.
  case H.
  left. apply singleton_iff_eq. reflexivity.
  right. apply singleton_iff_eq. reflexivity.
Qed.

Theorem in_or_to_in_unorder_pair:
  forall {U:Type}, forall {x y z:U}, z ∈ {| x |} \/ z ∈ {| y |} -> z ∈ (| x , y |).
  move => U x y z H.
  have Lx: z = x \/ z = y.
  case H => H0.
  left. apply singleton_iff_eq in H0. by [].
  right. apply singleton_iff_eq in H0. by [].
  case Lx => H0.
  rewrite H0. left.
  rewrite H0. right.
Qed.

Theorem in_unorder_pair_iff_in_or:
  forall {U:Type}, forall {x y z:U}, z ∈ (| x , y |) <-> z ∈ {| x |} \/ z ∈ {| y |}.
Proof.
  move => U x y z.
  rewrite /iff. split.
  apply in_unorder_pair_to_in_or.
  apply in_or_to_in_unorder_pair.
Qed.

Theorem unordered_pair_to_or:
  forall {U:Type}, forall {x y:U}, forall z':Collection U, (| x , y |) = z' -> (forall z:U, z ∈ z' <-> z = x \/ z = y).
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
  forall {U:Type}, forall {x y:U}, forall z':Collection U, (forall z:U, z ∈ z' <-> z = x \/ z = y) <-> (| x , y |) = z'.
Proof.
  move => U x y z'.
  rewrite /iff. split.
  apply unordered_pair_is_uniqueness.
  apply unordered_pair_to_or.
Qed.

Theorem unordered_pair_elements_is_sym:
  forall U:Type, forall {x y:U}, (| x , y |) = (| y , x |).
Proof.
  move => U x y.
  apply AxiomOfExtentionality => x0.
  rewrite /iff. split; case.
  apply unordered_pair_r. apply unordered_pair_l.
  apply unordered_pair_r. apply unordered_pair_l.
Qed.

Lemma singleton_eq_unordered_pair_to_and:
  forall U:Type, forall {a b c:U}, {| a |} = (| b , c |) -> a = b /\ b = c.
Proof.
  move => U a b c H.
  apply mutally_included_iff_eq in H.
  case: H => H0 H1.
  move: (H1 b) (H1 c) => H1b H1c.
  have L1: a=b.
  apply eq_sym.
  apply singleton_iff_eq.
  apply: H1b. apply unordered_pair_l.
  split.
  -by [].
  -apply eq_sym.
   apply singleton_iff_eq.
   rewrite -L1.
   apply H1c. apply unordered_pair_r.
Qed.

Lemma included_unorder_pair_to_and:
  forall U:Type, forall {a b c d:U}, (|a , b|) ⊂ (|c , d|) -> (a = c \/ a = d) /\ (b = c \/ b = d).
Proof.
  move => U a b c d H.
  split.
  move: (H a) => Ha.
  case: Ha.
  left.
  left. reflexivity.
  right. reflexivity.
  move: (H b) => Hb.
  case: Hb.
  right.
  left. reflexivity.
  right. reflexivity.
Qed.

Lemma unorder_pair_eq_to_or_l:
  forall U:Type, forall {a b c d:U}, (|a , b|) = (|c , d|) -> (a = c) \/ (a = d /\ b = c).
Proof.
  move => U a b c d H.
  apply mutally_included_iff_eq in H.
  case: H => H0 H1.
  apply included_unorder_pair_to_and in H0.
  apply included_unorder_pair_to_and in H1.
  case: H0 H1 => H0 H1.
  case => H2 H3.
  case H0 => H4.
  left. by [].
  right. split. by [].
  case: H1.
  apply.
  move => H5.
  have L1: a = b.
  rewrite H4 H5.
  reflexivity.
  apply eq_sym.
  case H2 => H6.
  rewrite H6.
  apply L1.
  apply H6.
Qed.

Lemma unorder_pair_eq_to_or_r:
  forall U:Type, forall {a b c d:U}, (|a , b|) = (|c , d|) -> (b = d) \/ (a = d /\ b = c).
Proof.
  move => U a b c d.
  move: unordered_pair_elements_is_sym => H.
  move: (H U a b) (H U c d) => H0 H1.
  rewrite H0 H1.
  move: unorder_pair_eq_to_or_l => Hl.
  have L1: b = d \/ b = c /\ a = d -> b = d \/ a = d /\ b = c.
  case => H2.
  left. by [].
  right.
  apply and_comm. by[].
  move => H2.
  apply L1.
  apply Hl. by [].
Qed.

Lemma unorder_pair_eq_to_or:
  forall U:Type, forall {a b c d:U}, (|a , b|) = (|c , d|) -> (a = c /\ b = d) \/ (a = d /\ b = c).
Proof.
  move => U a b c d H.
  apply LawOfDistributiveByOr.
  split.
  apply unorder_pair_eq_to_or_l in H. by [].
  apply unorder_pair_eq_to_or_r in H. by [].
Qed.

Inductive OrderedPair (U:Type) (x y:U) : Collection (Collection U) :=
| ordered_pair_first : In (Collection U) (OrderedPair U x y) (Singleton U x)
| ordered_pair_second : In (Collection U) (OrderedPair U x y) (UnorderedPair U x y).

Notation "<| x , y |>" := (OrderedPair _ x y).

Inductive FirstOfOrderedPair (U:Type) (XY: Collection (Collection U)) : Collection U :=
| ordered_pair_first_accessor: forall x:U, (exists y:U, <|x,y|> = XY) -> FirstOfOrderedPair U XY x.

Inductive SecondOfOrderedPair (U:Type) (XY: Collection (Collection U)) : Collection U :=
| ordered_pair_second_accessor: forall y:U, (exists x:U, <|x,y|> = XY) -> SecondOfOrderedPair U XY y.

Theorem ordered_pair_eq_unordered_pair:
  forall (U:Type), forall {a b:U}, <| a , b |> = (| {|a|} , (|a , b|) |).
Proof.
  move => U a b.
  apply AxiomOfExtentionality.
  move => x'.
  rewrite /iff. split.
  case. left. right.
  case. left. right.
Qed.

Theorem ordered_pair_to_and:
  forall (U:Type), forall {a b x y:U}, <| a , b |> = <| x , y |> -> a = x /\ b = y.
Proof.
  move => U a b x y H.
  rewrite ordered_pair_eq_unordered_pair in H.
  rewrite ordered_pair_eq_unordered_pair in H.
  apply unorder_pair_eq_to_or in H.
  case: H; case => H0 H1.
  apply singleton_eq_to_element_eq in H0.
  apply unorder_pair_eq_to_or in H1.
  case: H1 => H1. by[].
  split. by[].
  case: H1 => H2 H3.
  rewrite H0 in H2.
  rewrite H3. by [].
  apply singleton_eq_unordered_pair_to_and in H0.
  apply eq_sym in H1.
  apply singleton_eq_unordered_pair_to_and in H1.
  case: H0 H1 => H0 H1.
  case => H2 H3.
  split. by [].
  rewrite H0 in H3.
  rewrite H1 in H3.
  apply sym_eq in H3. by [].
Qed.
