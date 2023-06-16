From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.
Open Scope string_scope.

From CoqE2EAI Require Export string_tree.

(*returns the first subtree found on the specified path
  the path must not begin with the root node value*)
Fixpoint grab (path: list (list ascii)) (inputTree: tree) : option tree :=
  match path with
  | [] => Some inputTree
  | h::t => match find (fun n => (string_of_list_ascii h) =? (string_of_list_ascii (node_value n))) (node_children inputTree) with
              | Some found => grab t found
              | None => None
            end
end.

(*returns the value of the first child of the specified path
  the path must not begin with the root node value*)
Definition grab_value (path: list (list ascii)) (inputTree: tree) : option (list ascii) :=
  match grab path inputTree with
  | Some s => getFirstChildValue s
  | None => None
  end.

(*returns all children (with value child_name) of the first subtree found on the specified path
  the path must not begin with the root node value*)
Definition grabAll (path: list (list ascii)) (child_name: string) (inputTree: tree) : list tree :=
  let tree_opt := grab path inputTree in
  match tree_opt with
  | None => []
  | Some tree => match tree with
                 | leaf _ => []
                 | subtree _ c => filter (fun x => string_of_list_ascii (node_value x) =? child_name) c
                 end
end.



(*PROOFS*)

From Coq Require Import Nat.

Lemma emptyPath_grab: forall(t: tree), grab [] t = Some t.
Proof. intros. simpl. reflexivity. Qed.

Open Scope nat_scope.
Lemma notEmptyPath_grab_leaf: forall (path: list(list ascii))(value: list ascii),
  0 <? length path = true ->
    grab path (leaf value) = None.
Proof. intros. destruct path.
  - simpl in H. unfold ltb in H. unfold leb in H. discriminate H.
  - simpl. reflexivity. Qed.

Lemma notEmptyPath_grab_empty_children: forall (path: list(list ascii))(value: list ascii),
  0 <? length path = true ->
    grab path (subtree value []) = None.
Proof. intros. destruct path.
  - simpl in H. unfold ltb in H. unfold leb in H. discriminate H.
  - simpl. reflexivity. Qed.

Open Scope string_scope.
Lemma grab_value_app: forall (path: list(list ascii))(v value: list ascii)(a: tree)(children: list tree),
grab_value (path) (subtree value (a :: children)) = Some v ->
grab_value (path) (subtree value (children)) = Some v \/
grab_value (path) (subtree value [a]) = Some v.
Proof. intros. unfold grab_value in H. destruct (grab (path) (subtree value (a :: children))) eqn:D.
  - destruct path.
    + unfold grab_value. simpl. simpl in D. inversion D. rewrite <- H1 in H.
      unfold getFirstChildValue in H. simpl in H. unfold getFirstChildValue. simpl. right. apply H.
    + simpl in D. destruct (string_of_list_ascii l =? string_of_list_ascii (node_value a)) eqn:D2.
      * right. unfold grab_value. simpl. rewrite D2. rewrite D. apply H.
      * left. unfold grab_value. simpl. rewrite D. apply H.
  - inversion H. Qed.
