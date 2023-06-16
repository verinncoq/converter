From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Strings.Ascii.
From Coq Require Import BinNat.
From Coq Require Import Numbers.NatInt.NZDiv.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export split_string_dot.
From CoqE2EAI Require Export bitstrings.
From CoqE2EAI Require Export error_option.

Open Scope nat_scope.

(*returns true if c is a dot*)
Definition isDot (c: ascii) : bool :=
  let n:= Ascii.nat_of_ascii c in n =? 46.

(*
Helper for shift_dot_right.
Is called by that function.
Should not be called manually.
*)
Fixpoint shift_dot_right_rec (s buf: string) (times: nat) : string :=
  match times with
  | O   => match s with
           | EmptyString => buf
           | _           => buf ++ ("."%string ++ s)
           end
  | S n => match s with
           | EmptyString => shift_dot_right_rec EmptyString (append buf (String "0"%char ""%string)) n
           | String c t  => shift_dot_right_rec t (append buf (String c ""%string)) n
           end
  end.

(*
Moves the first found dot in the string 'times' times to the right. Zeros get appended if necessary.
I.e a shift-right operation is applied to the string representing a binary number.
If no dot is found, Error is returned.
*)
Definition shift_dot_right (s: string) (times: nat) : error_option string :=
  let d := split_string_dot_second s in
  match snd d with
  | EmptyString => Error "internal error: no dot found where some should be (shift_dot_right-function)."
  | String dot t => match (isDot dot) with
                    | false => Error "internal error: no dot found where some should be (shift_dot_right-function)."
                    | true => Success (append (fst d) (shift_dot_right_rec t ""%string times))
                    end
  end.

(*reverses the characters of the string*)
Definition reverse_string (s: string) : string :=
  string_of_list_ascii(rev (list_ascii_of_string s)).

(*
Helper for shift_dot_left.
Is called by that function.
Should not be called manually.
*)
Fixpoint shift_dot_left_rec (s buf: string) (times: nat) : string :=
  match times with
  | O   => match s with
           | EmptyString => buf ++ ".0"%string
           | _           => buf ++ ("."%string ++ s)
           end
  | S n => match s with
           | EmptyString => shift_dot_left_rec EmptyString (append buf (String "0"%char ""%string)) n
           | String c t  => shift_dot_left_rec t (append buf (String c ""%string)) n
           end
  end.

(*
Moves the first found dot in the string 'times' times to the left. Zeros get appended if necessary.
I.e a shift-left operation is applied to the string representing a binary number.
If no dot is found, Error is returned.
*)
Definition shift_dot_left (s: string) (times: nat) : error_option string :=
  let d := split_string_dot_first s in
  match reverse_string (fst d) with
  | EmptyString => Error "internal error: no dot found where some should be (shift_dot_left-function)."
  | String dot t => match (isDot dot) with
                    | false => Error "internal error: no dot found where some should be (shift_dot_left-function)."
                    | true => Success (append (reverse_string (shift_dot_left_rec (reverse_string t) ""%string times)) (snd d))
                    end
  end.

From Coq Require Import ZArith.
Open Scope Z_scope.

(*converts a Z (int) into a nat, with a bool representing the sign*)
Definition nat_of_Z (z: Z) : (bool * nat) :=
  match z with
  | Z0 => (false, 0%nat) (*zero is positive*)
  | Zpos p => (false, (Pos.to_nat p))
  | Zneg p => (true, (Pos.to_nat p))
  end.

Open Scope string_scope.

(*
Converts a string of length 32 consisting of 0 and 1 into a string representing a float.
This calls the IEEE standard for Floating-Point arithmetic (IEEE 754) for 32-bits in little-endian order.
If any requirement does not hold, Error is returned.
*)
Definition IEEE754 (bitstring: string) : error_option string :=
  match String.length bitstring with
  | 32%nat => match list_bool_of_string (substring 0 1 bitstring) with
              | Error e => Error e
              | Success sign => match list_bool_of_string (substring 1 8 bitstring) with
                             | Error e => Error e
                             | Success exponent => let mantissa := (substring 9 23 bitstring) in
                                                let B := 127%Z in
                                                let e := Z.sub (Z.of_nat (binary_to_decimal exponent)) B in
                                                let M := String.concat ""%string ["1."%string; mantissa] in
                                                let S := match sign with
                                                         | [true] => "-"%string
                                                         | [false] => ""%string
                                                         | _ => ""%string
                                                         end in
                                                let enat := nat_of_Z e in
                                                match fst enat with
                                                  | true =>  (*e is negative*) match shift_dot_left M (snd enat) with
                                                                               | Error e => Error e
                                                                               | Success n => Success (S ++ n) (*sign with number*)
                                                                               end
                                                  | false => (*e is positive*) match shift_dot_right M (snd enat) with
                                                                               | Error e => Error e
                                                                               | Success n => Success (S ++ n) (*sign with number*)
                                                                               end
                                                end
                             end
              end
  | _ => Error "IEEE754: The bitstring must contain exactly 32 bits."
  end.