From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export escapeSequenceExtractor.
From CoqE2EAI Require Export bitstrings.
From CoqE2EAI Require Export IEEE754.
From CoqE2EAI Require Export error_option.

(*Converts a bitstring representing a float into a readable float via IEEE754 (32-Bit).*)
Definition unpack (precision: nat) (s: list ascii) : error_option string :=
  match IEEE754 (little_endian (map bitstring_of_ascii s)) with
  | Error e => Error e
  | Success binfloat => bin_to_dec_z binfloat precision
  end.

(*Takes a list l, packs four items in a seperate list, concatenates theese lists and returns that as a list.*)
Fixpoint fourPacks {T: Type } (l: list T) : list (list T) :=
  match l with
  | [] => []
  | a::[] => [[a]]
  | a::b::[] => [[a; b]]
  | a::b::c::[] => [[a; b; c]]
  | a::b::c::d::t => [a; b; c; d]::(fourPacks t)
  end.

(*returns Success list if all list elements have type Success, Error otherwise*)
Fixpoint list_error_option_to_error_option_list {T: Type} (l: list (error_option T)) : error_option (list T) :=
  match l with
  | [] => Success []
  | h::t => match h with
            | Success e => match list_error_option_to_error_option_list t with
                        | Success t' => Success (e::t')
                        | Error e => Error e
                        end
            | Error e => Error e
            end
  end.

(*Unpacks sequences of 32-Bit bitstring using the unpack function (declared above). Escape Sequences might be used. Only for floats. *)
Definition unpack_mult (precision: nat) (s: string) : error_option (list string) :=
  match escapeSequenceExtractor (list_ascii_of_string s) with
  | Error e => Error e
  | Success seq => list_error_option_to_error_option_list (map (unpack precision) (fourPacks seq))
  end.

(*Compute unpack_mult 300 "\207\3330?b\370-\276\333\210\370\275\337a\036?".*)
