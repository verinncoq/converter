From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Nat.

From CoqE2EAI Require Import intermediate_representation.
(*functions to convert a list given a dimensionality into a scalar, vector or matrix*)


(*getIndex [get at some index]
returns Some T if l has value in index i. Returns None if not.*)
Fixpoint getIndex {T: Type}(l: list T)(i: nat): option T :=
  match l with
  | [] => None
  | h::t => match i with
            | O => Some h
            | S n => getIndex t n
            end
  end.

Open Scope string_scope.
(*returns float if l has value in index i. Returns 0 if not.*)
Fixpoint getIndex_optionZero (l: list string)(i: nat): string :=
  match l with
  | [] => "0.0"
  | h::t => match i with
            | O => h
            | S n => getIndex_optionZero t n
            end
  end.

(*get values*)

(*returns value specified by n and m. w is width of the matrix*)
Definition get_value_matrix_list_optionZero (w: nat)(l: list string)(m n: nat) : string :=
  getIndex_optionZero l ((n*w) + m).

Definition get_value_vector_list_optionZero (l: list string)(m: nat) : string :=
  getIndex_optionZero l m.


(*convertion*)

Definition IR_fixedValue_matrix_to_function (fv: IR_fixedValue): option (nat -> nat -> string) :=
  match fv with
  | value dim value_list => match dim with
                            | dim_scalar => None
                            | dim_vector x => None
                            | dim_matrix x y => Some (get_value_matrix_list_optionZero y value_list)
                            end
  end.

Definition IR_fixedValue_vector_to_function (fv: IR_fixedValue): option (nat -> string) :=
  match fv with
  | value dim value_list => match dim with
                            | dim_scalar => None
                            | dim_vector x => Some (get_value_vector_list_optionZero value_list)
                            | dim_matrix x y => None
                            end
  end.