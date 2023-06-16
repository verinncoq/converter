From Coq Require Import Bool.Bool.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
Local Open Scope string_scope.
From Coq Require Import Lists.List. Import ListNotations.

Local Open Scope lazy_bool_scope.

(*equality on list ascii wiht proofs about its correctness*)

(*inspired form coqs eqb function for strings,
see https://coq.inria.fr/library/Coq.Strings.String.html#eqb*)
Fixpoint eqb_la (s1 s2: list ascii) : bool :=
 match s1, s2 with
 | [], [] => true
 | h1::t1, h2::t2 => Ascii.eqb h1 h2 &&& eqb_la t1 t2
 | _,_ => false
 end.

(*Proof that this is the same as mentioned eqb for strings*)
Theorem eqb_la_eqb: forall (s t: list ascii),
eqb_la s t = eqb (string_of_list_ascii s) (string_of_list_ascii t).
Proof. induction s.
- destruct t.
  + simpl. reflexivity.
  + simpl. reflexivity.
- destruct t.
  + simpl. reflexivity.
  + simpl. rewrite <- IHs. reflexivity. Qed.

(*some proofs to show correctness,
inspired by https://coq.inria.fr/library/Coq.Strings.String.html#eqb_refl*)

Lemma eqb_la_refl: forall (x: list ascii),
eqb_la x x = true.
Proof. intros. rewrite eqb_la_eqb. apply eqb_refl. Qed.

Lemma eqb_la_sym: forall (x y: list ascii),
eqb_la x y = eqb_la y x.
Proof. intros. repeat (rewrite eqb_la_eqb). apply eqb_sym. Qed.

Lemma eqb_la_eq: forall (x y: list ascii),
eqb_la x y = true <-> x = y.
Proof. unfold iff. split.
- rewrite eqb_la_eqb. rewrite eqb_eq. intros. rewrite <- (list_ascii_of_string_of_list_ascii x).
  rewrite H. rewrite (list_ascii_of_string_of_list_ascii y). reflexivity.
- rewrite eqb_la_eqb. rewrite eqb_eq. intros. rewrite <- (list_ascii_of_string_of_list_ascii x).
  rewrite H. rewrite (list_ascii_of_string_of_list_ascii y). reflexivity. Qed.

Lemma eqb_la_neq: forall (x y: list ascii),
eqb_la x y = false <-> x <> y.
Proof. unfold iff. split.
- rewrite eqb_la_eqb. rewrite eqb_neq. intros. unfold not.
  intros. rewrite H0 in H. unfold not in H. destruct H. f_equal.
- rewrite eqb_la_eqb. rewrite eqb_neq. intros. unfold not.
  intros. unfold not in H. apply H. rewrite <- (list_ascii_of_string_of_list_ascii x).
  rewrite H0. rewrite (list_ascii_of_string_of_list_ascii y). reflexivity. Qed.
