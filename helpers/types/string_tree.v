From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.

From CoqE2EAI Require Export theorems.
From CoqE2EAI Require Export error_option.
From CoqE2EAI Require Export eqb_la.

(*type tree. used for the syntaxtree*)
Inductive tree :=
  | leaf (value : list ascii)
  | subtree (value: list ascii) (children : list tree).

(*type used to declare errors*)
Inductive StringErrorWarning :=
  | proper (value : list ascii)
  | error (value : list ascii) (error : list ascii)
  | warning (value : list ascii) (warning : list ascii).

(*type tree expanded with special nodes*)
Inductive tree_with_empty_and_error :=
  | empty
  | leaf_e (value : StringErrorWarning)
  | subtree_e (value: list ascii)(children : list tree_with_empty_and_error).

Fixpoint convertToEmptyAndError (t: tree) : tree_with_empty_and_error :=
  match t with
  | leaf v => leaf_e (proper v)
  | subtree v c => subtree_e v (map convertToEmptyAndError c)
  end.

(*converts a tree into a string*)
Fixpoint toString (t: tree) : string :=
  match t with
  | leaf v => string_of_list_ascii v
  | subtree v c => string_of_list_ascii v ++ concat ", " (map toString c)
  end.

Definition not_empty (e: tree_with_empty_and_error) : bool :=
  match e with
  | empty => false
  | _ => true
  end.

(*removes all appearances of empty, but keeps type as tree_with_empty*)
Fixpoint remove_empty (e : tree_with_empty_and_error) : tree_with_empty_and_error :=
  (*function assumes that root node is non-empty.
    This is okay because it is only used in the filter case, where every tree starts with a 'main' node,
    which won't be filtered.*)
  match e with
  | empty => empty
  | leaf_e v => leaf_e v
  | subtree_e v children => subtree_e v (filter not_empty (map remove_empty children))
  end.


(*converts tree_with_empty, does not remove empty nodes but replaces them instead with error node*)
Fixpoint convert_empty_without_removal (e : tree_with_empty_and_error) : tree_with_empty_and_error :=
  (*function assumes that root node is non-empty.
    This is okay because it is only used in the filter case, where every tree starts with a 'main' node,
    which won't be filtered.*)
  match e with
  | empty => leaf_e (error [] 
    (list_ascii_of_string "Error 1: empty rootnode detected, probably a failing of a previous function (internal error)"))
  | leaf_e v => leaf_e v
  | subtree_e v children => subtree_e v (map convert_empty_without_removal children)
  end.

(*converts tree_with_empty_and_error to tree, ignoring the errors and warning (assumes that there is no empty)*)
Fixpoint convert_tree (e: tree_with_empty_and_error) : tree :=
  (*function assumes that root node is non-empty.
    This is okay because it is only used in the filter case, where every tree starts with a 'main' node,
    which won't be filtered.*)
  match e with
  | empty => leaf []
  | leaf_e sew =>
    match sew with
    | proper v => leaf v
    | error v e => leaf v
    | warning v w => leaf v
    end
  | subtree_e v children => subtree v (map convert_tree children)
  end.

(*takes all error and warning string from the tree and concats them*)
Fixpoint convert_error_warning (e: tree_with_empty_and_error): string :=
  match e with
  | empty => "Error 1: internal error (in convert_error_warning, found empty-node which should have been removed).\n"
  | leaf_e sew =>
    match sew with
    | proper v => ""
    | error v e => append (string_of_list_ascii  e) "\n"
    | warning v w => append (string_of_list_ascii  w) "\n"
    end
  | subtree_e v children => concat "" (map convert_error_warning children)
  end.

(*converts tree_with_empty_and_error to tree, if error is found a Error type is returned*)
Definition convert_empty_error (e: tree_with_empty_and_error) : error_option tree :=
  let t := convert_empty_without_removal (remove_empty e) in
  let error_message := convert_error_warning t in
  match length error_message with
  | 0 => Success (convert_tree t)
  | _ => Error error_message
  end.

(*returns value of root node*)
Definition node_value (t : tree): list ascii :=
  match t with
  | leaf v => v
  | subtree v c => v
  end.

(*returns value of root node*)
Definition node_value_e (t : tree_with_empty_and_error): list ascii :=
  match t with
  | empty => []
  | leaf_e v => match v with
                | proper v => v
                | error v e => v
                | warning v w => v
                end
  | subtree_e v c => v
  end.

(*returns children of root node*)
Definition node_children (t : tree): list tree :=
  match t with
  | leaf v => []
  | subtree v c => c
  end.

(*returns value of first child, if found*)
Definition getFirstChildValue (t: tree): option (list ascii) :=
  let c := node_children t in 
  match c with
  | [] => None
  | h::t => Some (node_value h)
  end.

(*returns children of root node*)
Definition node_children_e (t : tree_with_empty_and_error): list tree_with_empty_and_error :=
  match t with
  | empty => []
  | leaf_e v => []
  | subtree_e v c => c
  end.

(*returns true if tree has type leaf or an empty children list*)
Definition is_leaf (t: tree) : bool :=
match t with
| leaf v => true
| subtree v c =>
  match c with
  | [] => true
  | _ => false
  end
end.

(*adds a new node to tree t, at the end of the children list
goes depth times down the tree, always choosing the last child
function used by parser to create syntaxtree
*)
Fixpoint append_at_end (t: tree) (depth: nat) (value: list ascii) : tree :=
  match depth with
  | O => subtree (node_value t) (app (node_children t) [subtree value []])
  | S n => subtree (node_value t) (app (removelast (node_children t))
           [append_at_end (last (node_children t) (leaf (list_ascii_of_string"probably_misplaced_node"))) n value])
  end.

(*only for debugging*)
Inductive stringtree :=
  | leaf_s (value : string)
  | subtree_s (value: string)(children : list stringtree).

Fixpoint toStringtree (t:tree): stringtree :=
match t with
| leaf v => leaf_s (string_of_list_ascii  v)
| subtree v c => subtree_s (string_of_list_ascii  v) (map toStringtree c)
end.

(*for Prooving
returns true if some list ascii is a value in tree t*)
Fixpoint InTree (s: list ascii) (t: tree): bool :=
match t with
| leaf v => eqb (string_of_list_ascii v) (string_of_list_ascii s)
| subtree v children => (eqb (string_of_list_ascii v) (string_of_list_ascii s)) || (existsb (InTree s) children)
end.

(*s must be a leaf (leaf or subtree with empty children list), otherwise false is returned*)
Fixpoint LeafInTree_r (s t: tree): bool :=
match s with
| leaf value_s =>
  match t with
  | leaf value_t => eqb (string_of_list_ascii value_s) (string_of_list_ascii value_t)
  | subtree value_t [] => eqb (string_of_list_ascii value_s) (string_of_list_ascii value_t)
  | subtree value_t children_t => (existsb (LeafInTree_r s) children_t)
  end
| subtree value_s [] => 
  match t with
  | leaf value_t => eqb (string_of_list_ascii value_s) (string_of_list_ascii value_t)
  | subtree value_t [] => eqb (string_of_list_ascii value_s) (string_of_list_ascii value_t)
  | subtree value_t children_t => (existsb (LeafInTree_r s) children_t)
  end
| _ => false
end.

Definition LeafInTree (s: list ascii)(t:tree): bool :=
LeafInTree_r (leaf s) t.

(*Proofs about InTree, inspired by proof about In from the standard library, 
beginning with https://coq.inria.fr/distrib/current/stdlib/Coq.Lists.List.html#in_eq*)

Lemma list_of_string_string_of_list: forall(s: list ascii),
s = list_ascii_of_string(string_of_list_ascii s).
Proof. induction s.
- simpl. reflexivity.
- simpl. rewrite <- IHs. reflexivity. Qed.

Lemma sol_eq: forall (s t: list ascii),
(eqb (string_of_list_ascii s) (string_of_list_ascii t)) = true -> s = t.
Proof. intros. rewrite list_of_string_string_of_list. rewrite eqb_eq in H. rewrite <- H.
rewrite <- list_of_string_string_of_list. reflexivity. Qed.

Lemma sol_neq: forall (s t: list ascii),
(eqb (string_of_list_ascii s) (string_of_list_ascii t)) = false -> s <> t.
Proof. intros. unfold not. rewrite eqb_neq in H. unfold not in H. intros.
rewrite <- list_ascii_of_string_of_list_ascii in H0. rewrite H0 in H.
rewrite list_ascii_of_string_of_list_ascii in H. apply H. reflexivity. Qed.

Lemma InTree_eq: forall (s: list ascii) (t: tree) (d: nat), InTree s (append_at_end t d s) = true.
Proof. intros. revert t. induction d.
- simpl. intros. rewrite orb_true_iff. right. rewrite existsb_app. rewrite orb_true_iff.
  right. simpl. rewrite orb_true_iff. left. rewrite orb_true_iff. left. rewrite eqb_refl. reflexivity.
- simpl. intros. rewrite orb_true_iff. right. rewrite existsb_app. rewrite orb_true_iff. right.
  simpl. rewrite orb_true_iff. left. apply IHd. Qed.

Lemma InTree_cons: forall (s r: list ascii) (t: tree) (d: nat),
InTree s t = true -> InTree s (append_at_end t d r) = true.
Proof. intros. revert H. revert t. induction d.
- simpl. intros. rewrite orb_true_iff. induction t.
  + left. simpl in H. unfold node_value. apply H.
  + rewrite existsb_app. rewrite orb_true_iff. unfold node_children. simpl in H.
    apply orb_true_iff in H. destruct H.
    * left. unfold node_value. apply H.
    * right. left. apply H.
- simpl. intros. rewrite orb_true_iff. induction t.
  + left. simpl in H. unfold node_value. apply H.
  + rewrite existsb_app. rewrite orb_true_iff. unfold node_children. unfold node_value. simpl in H.
    apply orb_true_iff in H. destruct H.
    * left. apply H.
    * right. destruct (existsb (InTree s) (removelast children)) eqn:L.
      -- left. reflexivity.
      -- right. destruct children.
        ++ simpl in H. discriminate.
        ++ assert (R: t :: children = removelast (t :: children) ++ [last (t::children) (leaf (list_ascii_of_string"probably_misplaced_node"))]). 
           ** assert (E: (t :: children) <> []). 
              --- unfold not. intro. discriminate H0.
              --- apply app_removelast_last. apply E.
           ** rewrite R in H. rewrite existsb_app in H. rewrite orb_true_iff in H. destruct H.
              --- rewrite H in L. discriminate L.
              --- unfold existsb. rewrite orb_true_iff. left. apply IHd. unfold existsb in H. rewrite orb_true_iff in H. destruct H.
                  ++++ apply H.
                  ++++ discriminate H. Qed.

Lemma InTree_not_app: forall (s r: list ascii) (t: tree) (d: nat),
InTree s (append_at_end t d r) = true /\ eqb (string_of_list_ascii r) (string_of_list_ascii s) = false ->
InTree s t = true \/ s = (list_ascii_of_string"probably_misplaced_node").
Proof. intros. destruct H. revert H. revert t. induction d.
- simpl. intros. rewrite orb_true_iff in H. destruct t.
  + simpl in H. destruct H.
    * simpl. left. apply H.
    * rewrite orb_true_iff in H. destruct H.
      -- rewrite orb_true_iff in H. destruct H.
         ++ rewrite H0 in H. discriminate.
         ++ discriminate.
      -- discriminate.
  + destruct H.
    * simpl in H. simpl. rewrite orb_true_iff. left. left. apply H.
    * simpl in H. simpl. rewrite orb_true_iff. left. right. rewrite existsb_app in H.
      rewrite orb_true_iff in H. destruct H.
      -- apply H.
      -- simpl in H. rewrite orb_true_iff in H. destruct H.
         ++ rewrite orb_true_iff in H. destruct H.
            ** rewrite H0 in H. discriminate.
            ** discriminate.
         ++ discriminate.
- intros. destruct t eqn:T.
  + simpl in H. rewrite orb_true_iff in H. destruct H.
    * simpl. left. apply H.
    * rewrite orb_true_iff in H. destruct H.
      -- simpl. apply IHd in H. right. destruct H.
         ++ unfold InTree in H. rewrite eqb_eq in H.
            rewrite list_of_string_string_of_list. rewrite H. 
            rewrite <- list_of_string_string_of_list. reflexivity.
         ++ rewrite H. simpl. reflexivity.
      -- discriminate.
  + simpl in H. rewrite orb_true_iff in H. destruct H.
    * left. simpl. rewrite orb_true_iff. left. apply H.
    * destruct children eqn:C.
      -- rewrite existsb_app in H. rewrite orb_true_iff in H. destruct H.
         ++ simpl in H. discriminate.
         ++ simpl in H. rewrite orb_true_iff in H. destruct H.
            ** apply IHd in H. destruct H.
               --- unfold InTree in H. right. simpl. rewrite eqb_eq in H.
                   rewrite list_of_string_string_of_list. rewrite H.
                   rewrite <- list_of_string_string_of_list. reflexivity.
               --- right. apply H.
            ** discriminate.
      -- assert(R: t0::l = removelast (t0::l) ++ [last (t0::l) (leaf (list_ascii_of_string"probably_misplaced_node"))]).
         ++ assert (E: (t0 :: l) <> []).
            ** unfold not. intros. discriminate H1.
            ** revert E. apply app_removelast_last.
         ++ rewrite existsb_app in H. rewrite orb_true_iff in H. destruct H.
            ** left. unfold InTree. rewrite orb_true_iff. right. rewrite R.
               rewrite existsb_app. rewrite orb_true_iff. left. apply H.
            ** unfold existsb in H. rewrite orb_true_iff in H. destruct H.
               --- apply IHd in H. destruct H.
                   +++ left. unfold InTree. rewrite orb_true_iff. right.
                       rewrite R. rewrite existsb_app. rewrite orb_true_iff. right. simpl. destruct l.
                       *** rewrite orb_true_iff. left. simpl in H. apply H. 
                       *** rewrite orb_true_iff. left. unfold InTree. simpl. simpl in H. apply H.
                   +++ right. apply H.
               --- discriminate. Qed.

Lemma append_at_end_depth_In: forall(s r: list ascii)(t: tree)(d1 d2: nat),
InTree s (append_at_end t d1 r) = true -> InTree s (append_at_end t d2 r) = true \/ s = list_ascii_of_string"probably_misplaced_node".
Proof. intros. destruct (eqb (string_of_list_ascii r) (string_of_list_ascii s)) eqn:E.
- apply eqb_eq in E. rewrite list_of_string_string_of_list at 1. rewrite <- E.
  rewrite <- list_of_string_string_of_list. left. apply InTree_eq.
- assert (C: InTree s (append_at_end t d1 r) = true /\ (string_of_list_ascii r =? string_of_list_ascii s)%string = false).
  + split.
    * apply H.
    * apply E.
  + apply InTree_not_app in C. destruct C.
    * left. apply InTree_cons. apply H0.
    * right. apply H0. Qed. 

Lemma InTree_inv: forall (s r: list ascii)(t: tree)(d: nat),
InTree s (append_at_end t d r) = true ->
eqb (string_of_list_ascii s) (string_of_list_ascii r) = true \/ InTree s t = true \/ s = (list_ascii_of_string"probably_misplaced_node").
Proof. intros. revert H. revert t. induction d.
- intros. simpl in H. rewrite orb_true_iff in H. destruct H.
  + right. induction t.
    * simpl. unfold node_value in H. left. apply H.
    * simpl. unfold node_value in H. rewrite orb_true_iff. left. left. apply H.
  + rewrite existsb_app in H. rewrite orb_true_iff in H. destruct H.
    * induction t .
      -- unfold node_children in H. simpl in H. discriminate.
      -- unfold node_children in H. right. simpl. rewrite orb_true_iff. left. right. apply H.
    * simpl in H. rewrite orb_true_iff in H. destruct H.
      -- rewrite orb_true_iff in H. destruct H.
         ++ left. apply eqb_eq in H. apply eqb_eq. symmetry. apply H.
         ++ discriminate.
      -- discriminate.
- induction t.
  + intros. simpl. simpl in H. rewrite orb_true_iff in H. destruct H.
    * right. left. apply H.
    * rewrite orb_true_iff in H. destruct H.
      -- apply IHd in H. destruct H.
         ++ left. apply H.
         ++ destruct H.
            ** unfold InTree in H. right. right. rewrite list_of_string_string_of_list.
               apply eqb_eq in H. rewrite H. rewrite <- list_of_string_string_of_list. reflexivity.
            ** right. right. rewrite list_of_string_string_of_list. 
               rewrite H. rewrite <- list_of_string_string_of_list. reflexivity.
      -- discriminate.
  + intros. apply (append_at_end_depth_In _ _ _ _ d) in H. destruct H.
    * apply IHd. apply H.
    * right. right. apply H. Qed.

Lemma LeafInTree_r_eq_leaf: forall(s: tree),
is_leaf s = true -> LeafInTree_r s s = true.
Proof. intros. destruct s. 
- simpl. apply eqb_eq. reflexivity.
- simpl. destruct children.
  + apply eqb_eq. reflexivity.
  + simpl in H. apply H. Qed.

Lemma LeafInTree_eq_leaf: forall(s: list ascii),
LeafInTree s (leaf s) = true.
Proof. intros. unfold LeafInTree. assert (H: is_leaf (leaf s) = true).
- simpl. reflexivity.
- revert H. apply LeafInTree_r_eq_leaf. Qed.

Lemma LeafInTree_r_eq_subtree: forall(s: tree)(c: list tree)(value: list ascii),
is_leaf s = true -> LeafInTree_r s (subtree value (s::c)) = true.
Proof. intros. destruct s.
- simpl. apply orb_true_iff. left. apply eqb_eq. reflexivity.
- destruct children.
  + simpl. apply orb_true_iff. left. apply eqb_eq. reflexivity.
  + simpl in H. discriminate H. Qed.

Lemma LeafInTree_r_cons: forall(s t: tree)(c: list tree)(value: list ascii),
is_leaf s = true -> (LeafInTree_r s (subtree value c) = true /\ c <> [] -> LeafInTree_r s (subtree value (t::c)) = true).
Proof. intros. destruct s.
- destruct c.
  + destruct H0. unfold not in H1. destruct H1. reflexivity.
  + simpl in H0. simpl. destruct H0. apply orb_true_iff in H0. destruct H0.
    * apply orb_true_iff. right. apply orb_true_iff. left. apply H0.
    * apply orb_true_iff. right. apply orb_true_iff. right. apply H0.
- destruct c.
  + destruct H0. unfold not in H1. destruct H1. reflexivity.
  + destruct children.
    * simpl in H0. simpl. destruct H0. apply orb_true_iff in H0. destruct H0.
      -- apply orb_true_iff. right. apply orb_true_iff. left. apply H0.
      -- apply orb_true_iff. right. apply orb_true_iff. right. apply H0.
    * simpl in H0. destruct H0. discriminate H0. Qed.

Lemma LeafInTree_r_nil: forall(s: tree)(value: list ascii),
s <> subtree value [] /\ s <> leaf value -> LeafInTree_r s (subtree value [])=false.
Proof. intros. destruct s.
- simpl. destruct H. apply eqb_neq. unfold not. intros. 
  apply string_of_list_constructer in H1. rewrite H1 in H0. destruct H0. reflexivity.
- destruct children.
  + simpl. destruct H. apply eqb_neq. unfold not. intros.
    apply string_of_list_constructer in H1. rewrite H1 in H. destruct H. reflexivity.
  + simpl. reflexivity. Qed.

Lemma LeafInTree_r_inv: forall(s t: tree)(c: list tree)(value: list ascii),
LeafInTree_r s (subtree value (t::c)) = true -> LeafInTree_r s t = true \/ LeafInTree_r s (subtree value c) = true.
Proof. intros. destruct s.
- simpl in H. apply orb_true_iff in H. destruct H.
  + left. apply H.
  + right. destruct c. 
    * simpl in H. discriminate H.
    * simpl. apply orb_true_iff. simpl in H. apply orb_true_iff in H. apply H.
- destruct children.
  + simpl in H. apply orb_true_iff in H. destruct H.
    * left. apply H.
    * right. destruct c. 
      -- simpl in H. discriminate H.
      -- simpl. apply orb_true_iff. simpl in H. apply orb_true_iff in H. apply H.
  + simpl in H. discriminate H. Qed.



(*unfinished proof
Lemma LeafInTree_r_InTree: forall(s: list ascii) (t:tree),
LeafInTree_r (leaf s) t = true \/ LeafInTree_r (subtree s []) t = true -> InTree s t = true.
Proof. intros. destruct t.
- simpl. destruct H.
  + simpl in H. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
  + simpl in H. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
- simpl. destruct H. 
  + induction children.
    * simpl. apply orb_true_iff. left. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
    * simpl in H. apply orb_true_iff in H. destruct H.
      -- apply orb_true_iff. right. simpl. apply orb_true_iff. left. destruct a.
         ++ simpl in H. simpl. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
         ++ simpl in H.

induction children.
  + simpl in H. destruct H.
    * apply orb_true_iff. left. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
    * apply orb_true_iff. left. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
  + simpl. simpl in H. destruct H.
    * apply orb_true_iff in H. destruct H.
      --




- destruct t.
  + simpl in H. simpl. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
  + destruct children.
    * simpl in H. simpl. apply orb_true_iff. left. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
    * simpl in H. simpl. apply orb_true_iff in H. destruct H.
      -- apply orb_true_iff. right. apply orb_true_iff. left. destruct t. 
         ++ simpl. simpl in H. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
         ++ induction children0.
            ** simpl. simpl in H. apply orb_true_iff. left. apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
            ** simpl. simpl in IHchildren0. 



 destruct a.
         ++ simpl in H. simpl. apply orb_true_iff. right. apply orb_true_iff.
            left. apply eqb_eq in H. apply eqb_eq. symmetry. apply H.
         ++ destruct children0.
            ** simpl in H. simpl. apply orb_true_iff. right.
               apply orb_true_iff. left. apply orb_true_iff. left.
               apply eqb_eq. apply eqb_eq in H. symmetry. apply H.
            ** simpl in H. apply orb_true_iff in H. destruct H.
               --- simpl.
*)


Open Scope string_scope.
(*equivalence on string_tree*)
Definition eq_string_tree (t1 t2: tree): Prop :=
match t1 with
| leaf v1 => match t2 with
             | leaf v2 => v1 = v2
             | subtree v2 [] => v1 = v2
             | subtree v2 (h2::t2) => False
             end
| subtree v1 [] => match t2 with
                   | leaf v2 => v1 = v2
                   | subtree v2 [] => v1 = v2
                   | subtree v2 c2 => False
                   end
| subtree v1 c1 => match t2 with
                   | leaf v2 => False
                   | subtree v2 c2 => v1 = v2 /\ c1 = c2
                   end
end.

(*PROOFS FOR eq_string_tree*)
Lemma eq_string_tree__reflexivity: forall (t: tree), eq_string_tree t t.
Proof. intros. destruct t.
  - simpl. reflexivity.
  - destruct children.
    + simpl. reflexivity.
    + simpl. split.
      * reflexivity.
      * reflexivity. Qed.

Lemma eq_string_tree__symmetry: forall (t1 t2: tree), eq_string_tree t1 t2 -> eq_string_tree t2 t1.
Proof. intros. destruct t1.
  - destruct t2.
    + simpl. simpl in H. symmetry. apply H.
    + destruct children.
      * simpl. simpl in H. symmetry. apply H.
      * simpl in H. inversion H.
  - destruct children.
    + destruct t2.
      * simpl. simpl in H. symmetry. apply H.
      * destruct children.
        -- simpl. simpl in H. symmetry. apply H.
        -- simpl in H. inversion H.
    + destruct t2.
      * simpl in H. inversion H.
      * destruct children0.
        -- simpl in H. destruct H. inversion H0.
        -- simpl. simpl in H. destruct H. split.
           ++ symmetry. apply H.
           ++ symmetry. apply H0. Qed.

Lemma eq_string_tree__transitivity: forall (t1 t2 t3: tree), eq_string_tree t1 t2 /\ eq_string_tree t2 t3 -> eq_string_tree t1 t3.
Proof. intros. destruct t1.
  - destruct t2.
    + destruct t3.
      * simpl. destruct H. simpl in H. simpl in H0. rewrite H. apply H0.
      * destruct children.
        -- simpl. destruct H. simpl in H. simpl in H0. rewrite H. apply H0.
        -- destruct H. simpl in H0. inversion H0.
    + destruct children.
      * destruct t3.
        -- destruct H. simpl in H. simpl in H0. rewrite H. apply H0.
        -- destruct children.
           ++ simpl. destruct H. simpl in H. simpl in H0. rewrite H. apply H0.
           ++ destruct H. simpl in H0. inversion H0.
      * destruct t3.
        -- destruct H. simpl in H. inversion H.
        -- destruct children.
           ++ simpl. destruct H. simpl in H. inversion H.
           ++ destruct H. simpl in H. inversion H.
  - destruct t2.
    + destruct t3.
      * destruct children.
        -- simpl. destruct H. simpl in H. simpl in H0. rewrite H. apply H0.
        -- destruct children.
           ++ destruct H. simpl in H. inversion H.
           ++ destruct H. simpl in H. inversion H.
      * destruct children.
        -- destruct children0.
           ++ simpl. destruct H. simpl in H. simpl in H0. rewrite H. apply H0.
           ++ destruct H. simpl in H0. inversion H0.
        -- simpl. destruct H. simpl in H. inversion H.
    + destruct children.
      * destruct t3.
        -- destruct children0.
           ++ simpl. destruct H. simpl in H. simpl in H0. rewrite H. apply H0.
           ++ destruct H. simpl in H0. inversion H0.
        -- destruct children0.
           ++ destruct children.
              ** simpl. destruct H. simpl in H. simpl in H0. rewrite H. apply H0.
              ** destruct H. simpl in H0. inversion H0.
           ++ destruct children.
              ** destruct H. simpl in H. inversion H.
              ** destruct H. simpl in H. inversion H.
      * destruct t3.
        -- destruct children0.
           ++ destruct children.
              ** destruct H. simpl in H. destruct H. inversion H1.
              ** destruct H. simpl in H. destruct H. inversion H1.
           ++ destruct children.
              ** destruct H. simpl in H0. inversion H0.
              ** destruct H. simpl in H0. inversion H0.
        -- destruct children0.
           ++ destruct children.
              ** destruct children1.
                 --- destruct H. simpl in H. destruct H. inversion H1.
                 --- destruct H. simpl in H. destruct H. inversion H1.
              ** destruct children1.
                 --- destruct H. simpl in H. destruct H. inversion H1.
                 --- destruct H. simpl in H0. inversion H0.
           ++ destruct children.
              ** destruct children1.
                 --- destruct H. simpl in H0. destruct H0. inversion H1.
                 --- destruct H. simpl in H0. destruct H0. simpl in H. destruct H. simpl. split.
                     +++ rewrite H. apply H0.
                     +++ rewrite H2. apply H1.
              ** destruct children1.
                 --- destruct H. simpl in H0. destruct H0. inversion H1.
                 --- destruct H. simpl in H0. destruct H0. simpl in H. destruct H. simpl. split.
                     +++ rewrite H. apply H0.
                     +++ rewrite H2. apply H1. Qed.
