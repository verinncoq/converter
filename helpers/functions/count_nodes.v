From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.


From CoqE2EAI Require Export string_tree.
From CoqE2EAI Require Export grab.

(*important function for proofs*)

(*counts how many children have value s*)
Fixpoint count_children (c: list tree)(s: string): nat :=
  match c with
  | [] => 0
  | h::t => match (string_of_list_ascii (node_value h)) =? s with
            | true => S (count_children t s)
            | false => count_children t s
            end
  end.

(*count s in graph field*)
Definition count (s: string) (t: tree): nat :=
  let nodes := grabAll (map list_ascii_of_string ["graph"]) s t in
  length nodes.

(*count all node types*)
Definition count_nodes (t: tree): nat :=
  (count "input" t) + (count "output" t) + (count "node" t) + (count "initializer" t).

(*count node type without input type*)
Definition count_nodes_without_input (t: tree): nat :=
  (count "output" t) + (count "node" t) + (count "initializer" t).


(*PROOFS*)
From Coq Require Import Nat.

Lemma count_leaf_zero: forall (v: list ascii)(s: string), count s (leaf v) = 0.
Proof. intros. unfold count. simpl. reflexivity. Qed.

Lemma count_emptySubtree_zero: forall (v: list ascii)(s: string), count s (subtree v []) = 0.
Proof. intros. unfold count. simpl. reflexivity. Qed.

Lemma count_nodes_leaf_zero: forall (v: list ascii), count_nodes (leaf v) = 0.
Proof. intros. unfold count_nodes. simpl. apply count_leaf_zero. Qed.

Lemma count_nodes_emptySubtree_zero: forall (v: list ascii), count_nodes (subtree v []) = 0.
Proof. intros. unfold count_nodes. simpl. apply count_emptySubtree_zero. Qed.

Lemma zero_nodes: forall (t: tree),
  count_nodes t = 0 -> (count "input" t) = 0 /\
                       (count "output" t) = 0 /\
                       (count "node" t) = 0 /\
                       (count "initializer" t) = 0.
Proof. intros. unfold count_nodes in H. split.
  - unfold add in H. repeat apply add_zero in H. apply H.
  - split.
    + apply add_zero in H; apply add_zero in H. rewrite add_comm in H. apply add_zero in H. apply H.
    + split.
      * apply add_zero in H. rewrite add_comm in H. apply add_zero in H. apply H.
      * rewrite add_comm in H. apply add_zero in H. apply H. Qed.

Lemma eq_string_tree__same_count: forall (t1 t2: tree),
  eq_string_tree t1 t2 -> count_nodes t1 = count_nodes t2.
Proof. intros. destruct t1.
  - destruct t2.
    + simpl in H. rewrite H. reflexivity.
    + destruct children.
      * simpl in H. rewrite H. unfold count_nodes. simpl. unfold count. simpl. reflexivity.
      * simpl in H. inversion H.
  - destruct t2.
    + destruct children.
      * unfold count_nodes. simpl. unfold count. simpl. reflexivity.
      * simpl in H. inversion H.
    + destruct children.
      * destruct children0.
        -- unfold count_nodes. simpl. unfold count. simpl. reflexivity.
        -- simpl in H. inversion H.
      * destruct children0.
        -- simpl in H. destruct H. inversion H0.
        -- assert(EQ: subtree value (t :: children) = subtree value0 (t0 :: children0)).
           ++ simpl in H. destruct H. rewrite H. rewrite H0. reflexivity.
           ++ rewrite EQ. reflexivity. Qed.

Lemma eq_string_tree__same_count_without_input: forall (t1 t2: tree),
  eq_string_tree t1 t2 -> count_nodes_without_input t1 = count_nodes_without_input t2.
Proof. intros. destruct t1.
  - destruct t2.
    + simpl in H. rewrite H. reflexivity.
    + destruct children.
      * simpl in H. rewrite H. unfold count_nodes. simpl. unfold count. simpl. reflexivity.
      * simpl in H. inversion H.
  - destruct t2.
    + destruct children.
      * unfold count_nodes. simpl. unfold count. simpl. reflexivity.
      * simpl in H. inversion H.
    + destruct children.
      * destruct children0.
        -- unfold count_nodes. simpl. unfold count. simpl. reflexivity.
        -- simpl in H. inversion H.
      * destruct children0.
        -- simpl in H. destruct H. inversion H0.
        -- assert(EQ: subtree value (t :: children) = subtree value0 (t0 :: children0)).
           ++ simpl in H. destruct H. rewrite H. rewrite H0. reflexivity.
           ++ rewrite EQ. reflexivity. Qed.
