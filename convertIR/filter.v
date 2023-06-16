From Coq Require Import Bool.Bool.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
Open Scope string_scope.
From Coq Require Import Lists.List. Import ListNotations.


From CoqE2EAI Require Export theorems.
From CoqE2EAI Require Export string_tree.
From CoqE2EAI Require Export inb.
From CoqE2EAI Require Export listStringToString.
From CoqE2EAI Require Export whitelist.
From CoqE2EAI Require Export count_nodes.

(*for error string creation*)
Definition supportedValues (a: list ascii): list ascii :=
let f := (get_value_whitelist a) in match f with
| whiteL v l => (list_ascii_of_string "only ") ++ (listToString l)
| blackL v l => (list_ascii_of_string "everything but ") ++ (listToString l)
end.

(*function is only applied to trees that have been filtered via filter_tree_filterListElement*)
Definition CreateWarningErrorMessage (parent: list ascii)(t: tree) : list ascii :=
match (eqb_la parent (list_ascii_of_string "op_type")) with
| true => 
  (list_ascii_of_string "Error 2: operation """)++
  (node_value t)++
  (list_ascii_of_string """ currently not supported. Supported opearations are ")++
  (supportedValues parent)
| false => list_ascii_of_string "Error 0: unknown error"
end.

Open Scope list_scope.
(*appends a to b, if both are Success. Else Error, with message of a or b (depending on if a is Error)*)
Definition append_option {T: Type}(a: error_option T)(b: error_option (list T)) : error_option (list T) :=
  match a with
  | Error s => Error s
  | Success la => match b with
                    | Error s => Error s
                    | Success lb => Success (la::lb)
                    end
   end.

(*returns a list, if all elements are Success. Returns Error else, with first errormessage found*)
Fixpoint extract_error (l: list (error_option tree)) : error_option (list tree) :=
  match l with
  | [] => Success []
  | h::t => append_option h (extract_error t)
  end.

(*helper for the filter, gets a tree (t) and the name of its parent node (parent)*)
Fixpoint filter_recursive (parent: list ascii) (t: tree) : error_option tree :=
  match t with
  | leaf value =>
    match (AttributesAcceptsValue parent value) with
    | true => Success (leaf value) (*no error*)
    | false => Error (string_of_list_ascii (CreateWarningErrorMessage parent t)) (*error*)
    end
  | subtree value [] => (*subtrees with no children are acutally leafs*)
    match (AttributesAcceptsValue parent value) with
    | true => Success (leaf value) (*no error*)
    | false => Error (string_of_list_ascii (CreateWarningErrorMessage parent t)) (*error*)
    end
  | subtree value children => let filtered_children := map (filter_recursive value) children in
                              let error := extract_error filtered_children in
                              match error with
                              | Error s => Error s
                              | Success c => Success (subtree value children)
                              end
  end.

(*
Filter function. Takes a tree, with 'main' as a parent name for the root node.
*)
Definition filter (t: tree): error_option tree :=
  filter_recursive (list_ascii_of_string "main") t.



(*PROOFS*)
Lemma no_error_same_tree: forall(t ft: tree),
filter t = Success ft -> eq_string_tree t ft.
Proof. intros. destruct t.
  - unfold filter in H. simpl in H. unfold convert_empty_error in H. simpl in H. inversion H. reflexivity.
  - destruct children.
    + unfold filter in H. simpl in H. unfold convert_empty_error in H. simpl in H. inversion H. reflexivity.
    + unfold filter in H. simpl in H. destruct (append_option (filter_recursive value t)
        (extract_error (map (filter_recursive value) children))).
      * inversion H. apply eq_string_tree__reflexivity.
      * inversion H. Qed.


Theorem no_error_implies_same_node_count: forall (t ft: tree),
filter t = Success ft -> count_nodes t = count_nodes ft.
Proof. intros. apply no_error_same_tree in H. apply eq_string_tree__same_count. apply H. Qed.

Theorem no_error_implies_same_node_count_without_input: forall (t ft: tree),
filter t = Success ft -> count_nodes_without_input t = count_nodes_without_input ft.
Proof. intros. apply no_error_same_tree in H. apply eq_string_tree__same_count_without_input. apply H. Qed.

Lemma filter_app: forall(children: list tree)(a: tree)(value: list ascii),
isError (filter (subtree value (a :: children))) = true <->
isError (filter_recursive value a) = true \/ 
isError (filter (subtree value children)) = true.
Proof. unfold iff. split.
  - intros. unfold filter in H. simpl in H. destruct (filter_recursive value a) eqn:D1.
    + destruct (append_option (Success t) (extract_error (map (filter_recursive value) children))) eqn:D2.
      * inversion H.
      * right. destruct children.
        -- simpl in D2. inversion D2.
        -- unfold filter. simpl. simpl in D2.
           destruct (append_option (filter_recursive value t0) (extract_error (map (filter_recursive value) children))).
           ++ inversion D2.
           ++ inversion D2. apply H.
    + left. simpl in H. apply H.
  - intros. destruct H.
    + unfold filter. simpl. destruct (filter_recursive value a). 
      * inversion H. 
      * simpl. apply H.
    + destruct children.
      * unfold filter in H. simpl in H. inversion H.
      * unfold filter. simpl. unfold filter in H. simpl in H. destruct (append_option (filter_recursive value t)
        (extract_error (map (filter_recursive value) children))) eqn:D.
        -- inversion H.
        -- unfold append_option. destruct (filter_recursive value a) eqn:D2.
           ++ apply H.
           ++ unfold isError. simpl. reflexivity. Qed.

(*unfinished proof, that says if a value is not accepted by its parent, an error is thrown*)
Open Scope string_scope.
Theorem not_allowed_value_leaf: forall (t g: tree)(p: list (list ascii))(k v: list ascii),
grab_value (rev (k::p)) t = Some v /\
AttributesAcceptsValue k v = false ->
isError (filter t) = true.
Proof. Abort.

