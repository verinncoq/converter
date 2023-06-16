From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Nat.
From Coq Require Import Lists.List.
From Coq Require Import Sorting.Permutation.

From CoqE2EAI Require Import in_edges_coq.
From CoqE2EAI Require Import out_edges_coq.

Open Scope string_scope.

Fixpoint indegree (node: string) (edges: list(string * string)): nat :=
  match edges with 
  | [] => 0
  | (n1, n2)::rest => (if n2=?node then S (indegree node rest) else (indegree node rest))
end.


Fixpoint outdegree (node: string) (edges: list(string * string)): nat :=
  match edges with 
  | [] => 0
  | (n1, n2)::rest => (if n1=?node then S (outdegree node rest) else (outdegree node rest))
end.


Fixpoint In (a:string) (l:list string): bool :=
  match l with
  | [] => false
  | b::rest => if a=?b then true else (In a rest)
end.

Open Scope nat_scope.

Fixpoint indegree_signature_helper (edges: list (string*string)) (exhausted: list string): list nat :=
  match edges with
  | [] => []
  | (n1, n2)::rest => if ((In n2 exhausted)) then (indegree_signature_helper rest exhausted) else
                                           [(indegree n2 edges)]++(indegree_signature_helper rest (exhausted ++[n2]))
end.

Definition indegree_signature (edges: list (string*string)): list nat := indegree_signature_helper edges [].

Fixpoint outdegree_signature_helper (edges: list (string*string)) (exhausted: list string): list nat :=
  match edges with
  | [] => []
  | (n1, n2)::rest => if ((In n1 exhausted)) then (outdegree_signature_helper rest exhausted) else
                                           [(outdegree n1 edges)]++(outdegree_signature_helper rest (exhausted ++[n1]))
end.

Definition outdegree_signature (edges: list (string*string)): list nat := outdegree_signature_helper edges [].


Fixpoint remove (elem: nat) (l: list nat) : list nat :=
  match l with
  | [] => []
  | x::rest => if elem=?x then rest else x::(remove elem rest)
end.


Fixpoint permutation (E1 E2: list nat) : Prop :=
  match E1 with
  | [] => match E2 with
           | [] => True
           | _::_ => False
           end
  | x::rest => match E2 with
               | [] => False
               | _::_ => permutation rest (remove x E2) 
               end
end.

Definition isomorphic (G1 G2: list (string*string)): Prop :=
  (permutation (indegree_signature G1) (indegree_signature G2))
  /\ (permutation (outdegree_signature G1) (outdegree_signature G2)).

Compute (isomorphic in_edges_coq.onnx_edges out_edges_coq.coq_edges).

(* PROOFS 
Lemma zero_deg_if_empty: forall (node: string),
  indegree node [] = 0 /\ outdegree node [] = 0.
Proof.
intros. split. 
  - unfold indegree. reflexivity.
  - unfold outdegree. reflexivity.
Qed.

Lemma remove_length_noninc: forall (E: list nat) (n: nat), length E >= length (remove n E).
Proof.
intros. induction E.
  - auto.
  - simpl. destruct (n=?a) eqn:eq.
    + auto.
    + simpl. apply le_n_S. apply IHE.
Qed.

Lemma perm_nil: forall (E: list nat), permutation [] E -> E = [].
Proof.
intros. destruct E.
  - reflexivity.
  - inversion H.
Qed.

Lemma perm_app: forall (E1 E2: list nat) (n:nat), permutation E1 E2 -> permutation (n::E1) (n::E2).
Proof.
intros. simpl. rewrite PeanoNat.Nat.eqb_refl. assumption.
Qed.

Lemma perm_refl: forall (E: list nat), permutation E E.
Proof.
intros. induction E. reflexivity. apply perm_app. assumption.
Qed.

Lemma perm_length: forall (E1 E2: list nat), permutation E1 E2 -> length E1 = length E2.
Proof.
intros. induction E1 eqn:e1.
  - apply perm_nil in H. rewrite H. auto.
  - destruct E2 eqn:e2.
    + unfold permutation in H. tauto.
    + rewrite e1 in IHl.

Lemma perm_symmetric: forall (E1 E2: list nat), permutation E1 E2 -> permutation E2 E1.
Proof.
intros. induction E1 eqn:IHE.
  - destruct E2.
    + reflexivity.
    + inversion H.
  - destruct (a::l) eqn:equal.
    + inversion equal.
*)