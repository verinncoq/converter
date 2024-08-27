Require Import Floats.
Require Import Reals.
From Coq Require Import String.

From CoqE2EAI Require Export string_tree.



(*
This document describes the types used for different intermediate representations, 
as well as usefull methods on it

1: the FOURTUPLE type and subtypes
2: the INTERMEDIATE REPRESENTATION 1
3: the PREMODEL
4: the CONNECTED NETWORK (unused)
*)


(*1*)

(*the fourtuple is just a tuple of four lists:
  1: input 
  2: output
  3: nodes
  4: initializers
*)
Inductive fourtuple (T: Type) :=
  | ft: (list T * list T * list T * list T) -> fourtuple T.

Definition get_input {T: Type}(t: fourtuple T): list T :=
  match t with
  | ft _ tuple => fst (fst (fst tuple))
  end.
Definition get_output {T: Type}(t: fourtuple T): list T :=
  match t with
  | ft _ tuple => snd (fst (fst tuple))
  end.
Definition get_nodes {T: Type}(t: fourtuple T): list T :=
  match t with
  | ft _ tuple => snd (fst tuple)
  end.
Definition get_initializer {T: Type}(t: fourtuple T): list T :=
  match t with
  | ft _ tuple => snd tuple
  end.

Definition flatten_fourtuple {T: Type}(t: fourtuple T): list T :=
  (get_input t) ++ (get_output t) ++ (get_nodes t) ++ (get_initializer t).

Definition flatten_fourtuple_without_output {T: Type}(t: fourtuple T): list T :=
  (get_input t) ++ (get_nodes t) ++ (get_initializer t).

Definition flatten_fourtuple_without_input {T: Type}(t: fourtuple T): list T :=
  (get_output t) ++ (get_nodes t) ++ (get_initializer t).


(*2*)

(*Used to denotate a dimensionality of either
   a scalar which has no input
   a vector which takes one dimensionality input
   a matrix which takes two dimensionality inputs
*)
Inductive IR_dim :=
| dim_scalar: IR_dim
| dim_vector: nat -> IR_dim
| dim_matrix: nat -> nat -> IR_dim.

(*Used to construct scalars, vectors and matrices*)
Inductive IR_fixedValue :=
| value: IR_dim -> list string -> IR_fixedValue.

(*all types of allowed operations so far. When adding a new one, it should be added here
  see https://github.com/onnx/onnx/blob/main/docs/Operators.md for documentation of the operations
      gemm: takes 4 attributes: alpha, beta, transA, transB
      relu: no arguments needed
*)
Inductive IR_operation :=
| gemm: string -> string -> string -> string -> IR_operation
| relu: IR_operation.

(*The four types of elements, coming from the 4-tuple of 'prepare_data'
    IR_input(name, dimensionality);
    IR_output(name, dimensionality);
    IR_node(name, input_names, output_names, called_operation);
    IR_initializer(name, value)
*)
Inductive IR_elem :=
| IR_input: string -> IR_dim -> IR_elem
| IR_output: string -> IR_dim -> IR_elem
| IR_node: string -> list string -> list string -> IR_operation -> IR_elem
| IR_initializer: string -> IR_fixedValue -> IR_elem.

(*converts an IR_elem into a string (debug only)*)
Definition toStringIR (ir: IR_elem) : string :=
  match ir with
  | IR_input name dim => "input: " ++ name
  | IR_output name dim => "output: " ++ name
  | IR_node name inputs outputs operation => "node: " ++ name
  | IR_initializer name v => "initializer: " ++ name
  end.

(*3*)
(*for coq-simple-io and python export*)
Inductive NNPremodel :=
| NNPremodel_initializer_matrix: string -> nat -> nat -> (nat -> nat -> string) -> NNPremodel
| NNPremodel_initializer_vector: string -> nat -> (nat -> string) -> NNPremodel
| NNPremodel_Output: string -> nat -> NNPremodel
| NNPremodel_Linear: string -> string -> string -> string -> string -> string -> NNPremodel
| NNPremodel_ReLu: string -> string -> NNPremodel.


(*4*)
(*try on a connected network, unused*)
Inductive IR_connected_elem :=
| IR_connected_input: string -> IR_dim -> IR_connected_elem
| IR_connected_output: IR_connected_elem -> IR_dim -> IR_connected_elem
| IR_connected_node: list IR_connected_elem -> IR_operation -> IR_connected_elem
| IR_connected_initializer: IR_fixedValue -> IR_connected_elem.
