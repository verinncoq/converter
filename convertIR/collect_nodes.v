From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export grab.
From CoqE2EAI Require Export error_option.
From CoqE2EAI Require Export intermediate_representation.
From CoqE2EAI Require Export count_nodes.

Open Scope string_scope.

(*Converts tree to fourtuple tree, containing lists of: input, output, node and initializer*)
Definition collect_nodes (t: tree) : fourtuple tree :=
  ft tree (
    (grabAll (map list_ascii_of_string ["graph"]) "input" t),
    (grabAll (map list_ascii_of_string ["graph"]) "output" t),
    (grabAll (map list_ascii_of_string ["graph"]) "node" t),
    (grabAll (map list_ascii_of_string ["graph"]) "initializer" t)
  ).

(*checks if some list in fourtuple is empty*)
Definition check_extracted_nodes (d: fourtuple tree) : bool :=
  match length (get_input d) with
  | O => false
  | S _ => match length (get_output d) with
           | O => false
           | S _ => match length (get_nodes d) with
                    | O => false
                    | S _ => match length (get_initializer d) with
                             | O => false
                             | S _ => true
                             end
                    end
            end
  end.

(*PROOFS*)

Lemma same_node_count_collect_nodes_input: forall (t: tree),
  length (get_input (collect_nodes t)) = count "input" t.
Proof. intros. unfold collect_nodes. unfold get_input. unfold fst. unfold count. reflexivity. Qed.

Lemma same_node_count_collect_nodes_output: forall (t: tree),
  length (get_output (collect_nodes t)) = count "output" t.
Proof. intros. unfold collect_nodes. unfold get_output. unfold fst. unfold snd. unfold count. reflexivity. Qed.

Lemma same_node_count_collect_nodes_nodes: forall (t: tree),
  length (get_nodes (collect_nodes t)) = count "node" t.
Proof. intros. unfold collect_nodes. unfold get_nodes. unfold fst. unfold snd. unfold count. reflexivity. Qed.

Lemma same_node_count_collect_nodes_initializer: forall (t: tree),
  length (get_initializer (collect_nodes t)) = count "initializer" t.
Proof. intros. unfold collect_nodes. unfold get_initializer. unfold fst. unfold snd. unfold count. reflexivity. Qed.

Theorem same_node_count_collect_nodes: forall (t: tree),
  length (flatten_fourtuple (collect_nodes t)) = count_nodes t.
Proof. intros. unfold collect_nodes. unfold flatten_fourtuple.
unfold get_input. unfold get_output. unfold get_nodes. unfold get_initializer.
unfold count_nodes. unfold count. unfold fst. unfold snd. repeat rewrite add_len. repeat rewrite nat_ass. reflexivity. Qed.

Theorem same_node_count_collect_nodes_without_input: forall (t: tree),
  length (flatten_fourtuple_without_input (collect_nodes t)) = count_nodes_without_input t.
Proof. intros. unfold collect_nodes. unfold flatten_fourtuple_without_input.
unfold get_output. unfold get_nodes. unfold get_initializer.
unfold count_nodes_without_input. unfold count. unfold fst. unfold snd. repeat rewrite add_len. repeat rewrite nat_ass. reflexivity. Qed.