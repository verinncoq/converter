From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
Open Scope string_scope.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export eqb_la.
From CoqE2EAI Require Export inb.
From CoqE2EAI Require Export string_tree.

(*
whitelist for the filter module. Elements can define either a blacklist,
  containing all the forbidden children names, or a whitelist,
  containing all the allowed elements
*)
Inductive filterListElement :=
| whiteL (a: (list ascii))(v: list (list ascii))
| blackL (a: (list ascii))(v: list (list ascii)).


Definition whitelist: list (filterListElement) := [
blackL (list_ascii_of_string "main") [];
blackL (list_ascii_of_string "graph") [];
blackL (list_ascii_of_string "name") [];
blackL (list_ascii_of_string "node") [];
blackL (list_ascii_of_string "input") [];
blackL (list_ascii_of_string "output") [];
whiteL (list_ascii_of_string "op_type") (map list_ascii_of_string ["""Gemm""";"""Relu"""]);
blackL (list_ascii_of_string "attribute") [];
blackL (list_ascii_of_string "type") [];
blackL (list_ascii_of_string "f") [];
blackL (list_ascii_of_string "i") [];
blackL (list_ascii_of_string "s") [];
blackL (list_ascii_of_string "t") [];
blackL (list_ascii_of_string "g") [];
blackL (list_ascii_of_string "floats") [];
blackL (list_ascii_of_string "ints") [];
blackL (list_ascii_of_string "strings") [];
blackL (list_ascii_of_string "tensors") [];
blackL (list_ascii_of_string "graphs") [];
blackL (list_ascii_of_string "initializer") [];
blackL (list_ascii_of_string "dims") [];
blackL (list_ascii_of_string "data_type") [];
blackL (list_ascii_of_string "float_data") [];
blackL (list_ascii_of_string "int32_data") [];
blackL (list_ascii_of_string "string_data") [];
blackL (list_ascii_of_string "int64_data") [];
blackL (list_ascii_of_string "raw_data") [];
blackL (list_ascii_of_string "input") [];
blackL (list_ascii_of_string "type") [];
blackL (list_ascii_of_string "elem_type") [];
blackL (list_ascii_of_string "shape") [];
blackL (list_ascii_of_string "dim") [];
blackL (list_ascii_of_string "dim_value") [];
blackL (list_ascii_of_string "dim_param") [];
blackL (list_ascii_of_string "key_type") [];
blackL (list_ascii_of_string "value_type") [];
blackL (list_ascii_of_string "output") [];
blackL (list_ascii_of_string "tensor_type") [];
blackL (list_ascii_of_string "data_converted") []
].

(*returns the attribute*)
Definition getAttribute (e: filterListElement) :=
match e with
| whiteL a v => a
| blackL a v => a
end.

(*returns the list of attributes in the whitelist*)
Definition attribute_whitelist := map getAttribute whitelist.

(*returns the first filterListElement in w matching the attribute a*)
Fixpoint get_value_whitelist_r (a: list ascii)(w: list filterListElement) : filterListElement :=
match w with
| [] => blackL a []
| h::t =>
  match eqb_la (getAttribute h) a with
  | true => h
  | false => get_value_whitelist_r a t
  end
end.

(*returns the first filterListElement in whitelist matching the attribute a*)
Definition get_value_whitelist (a: list ascii) : filterListElement :=
get_value_whitelist_r a whitelist.

(*return wether an attributes gets accepted by its parent. is used in filter function*)
Definition AttributesAcceptsValue (a v: list ascii) : bool :=
let f := (get_value_whitelist a) in match f with
| whiteL a v' => Inb v' v
| blackL a v' => notInb v' v
end.