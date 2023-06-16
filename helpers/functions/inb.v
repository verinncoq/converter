From Coq Require Import Bool.Bool.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.

Open Scope string_scope.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export string_tree.


(*source: https://coq.inria.fr/library/Coq.Lists.List.html#In*)
(*Function In from coqs standard library has been changed to produce bool output instead of prop*)
(*also list input in now specified to string and order of arguments changed to use it as filter input*)
Fixpoint Inb (l: list (list ascii))(s: (list ascii)) : bool :=
  match l with
  | [] => false
  | b :: m => 
    if (eqb (string_of_list_ascii b) (string_of_list_ascii s)) then true
    else Inb m s
  end.

(*used in whitelist, in a filter function, so the Inb function could not be reversed*)
Fixpoint notInb (l: list (list ascii))(s: (list ascii)) : bool :=
  match l with
  | [] => true
  | b :: m => 
    if (eqb (string_of_list_ascii b) (string_of_list_ascii s)) then false
    else notInb m s
  end.

Theorem negb_Inb_notInb: forall (l: list (list ascii))(s: (list ascii)),
negb (Inb l s) = notInb l s.
Proof. induction l.
- simpl. reflexivity.
- intros. simpl. rewrite <- orb_lazy_alt. rewrite negb_orb.
  assert(H: string_of_list_ascii a =? string_of_list_ascii s = negb (negb (string_of_list_ascii a =? string_of_list_ascii s))).
  * rewrite negb_involutive. reflexivity.
  * rewrite H at 2. rewrite if_negb. rewrite <- andb_lazy_alt. rewrite IHl. reflexivity. Qed.

Theorem Inb_is_true_implies_In_is_true: forall (s:(list ascii)) (l:list (list ascii)),
(Inb l s = true) -> In s l.
Proof. intros s l. induction l.
  - simpl. intros H. inversion H.
  - simpl. destruct ((eqb (string_of_list_ascii a) (string_of_list_ascii s))) as []eqn:?.
    * intros H. left. rewrite eqb_eq in Heqb. rewrite <- list_ascii_of_string_of_list_ascii.
      rewrite <- Heqb. rewrite <- list_of_string_string_of_list. reflexivity.
    * intros H. right. apply IHl in H. apply H. Qed.

Theorem In_is_true_implies_Inb_is_true: forall (s:(list ascii)) (l:list (list ascii)),
  In s l -> (Inb l s = true).
Proof. intros s l. induction l.
  - simpl. intros H. inversion H.
  - simpl. destruct ((eqb (string_of_list_ascii a) (string_of_list_ascii s))) as []eqn:?.
    * intros H. reflexivity.
    * intros H. apply IHl. destruct H.
      + rewrite eqb_neq in Heqb. unfold not in Heqb. rewrite H in Heqb. contradiction.
      + apply H. Qed.

Theorem Inb_is_false_implies_In_is_false: forall (s:(list ascii)) (l:list (list ascii)),
  (Inb l s = false) -> ~ In s l.
Proof. intros s l. induction l.
  - simpl. intros H. unfold not. contradiction.
  - simpl. destruct ((eqb (string_of_list_ascii a) (string_of_list_ascii s))) as []eqn:?.
    * intros H. unfold not. intros H2. inversion H.
    * intros H. unfold not. intros H2. destruct H2.
      + rewrite eqb_neq in Heqb. unfold not in Heqb. rewrite H0 in Heqb. contradiction.
      + apply IHl in H. contradiction. Qed.

Theorem In_is_false_implies_Inb_in_false: forall (s:(list ascii)) (l:list (list ascii)),
  ~ In s l -> (Inb l s = false).
Proof. intros s l. induction l.
  - simpl. intros H. reflexivity.
  - simpl. destruct ((eqb (string_of_list_ascii a) (string_of_list_ascii s))) as []eqn:?.
    * intros H. unfold not in H. destruct H. left. apply eqb_eq in Heqb. rewrite <- list_ascii_of_string_of_list_ascii.
      rewrite <- Heqb. rewrite <- list_of_string_string_of_list. reflexivity.
    * intros H. unfold not in H. apply IHl. unfold not. intros H2. destruct H. right. apply H2. Qed.

Theorem In_Inb_eq2: forall (s:(list ascii)) (l:list (list ascii)), In s l <-> Is_true (Inb l s).
Proof. intros s l. unfold iff. split.
  - unfold Is_true. destruct (Inb l s) as []eqn:?.
    + intros H. reflexivity.
    + intros H. apply Inb_is_false_implies_In_is_false in Heqb. contradiction.
  - unfold Is_true. destruct (Inb l s) as []eqn:?.
    + intros H. apply Inb_is_true_implies_In_is_true in Heqb. apply Heqb.
    + intros H. contradiction. 
 Qed.


