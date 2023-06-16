(*this file is inspired by 
  https://stackoverflow.com/questions/15334909/convert-function-from-string-to-nat-in-coq*)
(*file useful when executing output file of converter, defining functions to convert strings to numbers*)

From Coq Require Import String Ascii.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Nat.
From Coq Require Import Reals.

Open Scope string_scope.

Definition nat_of_ascii (c: ascii) : option nat :=
 match c with
(* Zero is 0011 0000 *)
   | Ascii false false false false true true false false => Some 0
(* One is 0011 0001 *)
   | Ascii true false false false true true false false => Some 1
(* Two is 0011 0010 *)
   | Ascii false true false false true true false false => Some 2
   | Ascii true true false false true true false false => Some 3
   | Ascii false false true false true true false false => Some 4
   | Ascii true false true false true true false false => Some 5
   | Ascii false true true false true true false false => Some 6
   | Ascii true true true false true true false false => Some 7
   | Ascii false false false true true true false false => Some 8
   | Ascii true false false true true true false false => Some 9
   | _ => None
end.

Fixpoint nat_of_string_r (s : list ascii) : option nat :=
  match s with
  | [] => Some O
  | h::t => match (nat_of_ascii h), (nat_of_string_r t) with
            | Some n, Some m => Some (n + 10 * m)
            | _ , _ => None
            end
  end.

Definition nat_of_string (s : list ascii): option nat := nat_of_string_r (rev s).

(*Highest Nat that didn't cause a stack overflow in my enviroment*)
(*Compute nat_of_string (list_ascii_of_string "149692").*)

(* floats removed
Open Scope float_scope.

Definition float_of_ascii (c: ascii) : option float :=
 match c with
(* Zero is 0011 0000 *)
   | Ascii false false false false true true false false => Some 0
(* One is 0011 0001 *)
   | Ascii true false false false true true false false => Some 1
(* Two is 0011 0010 *)
   | Ascii false true false false true true false false => Some 2
   | Ascii true true false false true true false false => Some 3
   | Ascii false false true false true true false false => Some 4
   | Ascii true false true false true true false false => Some 5
   | Ascii false true true false true true false false => Some 6
   | Ascii true true true false true true false false => Some 7
   | Ascii false false false true true true false false => Some 8
   | Ascii true false false true true true false false => Some 9
   | _ => None
end.

Fixpoint float_of_string_r (s : list ascii) : option float :=
  match s with
  | [] => Some 0
  | h::t => match (float_of_ascii h), (float_of_string_r t) with
            | Some n, Some m => Some (n + 10 * m)
            | _ , _ => None
            end
  end.

Definition float_of_string_minor (s : list ascii): option float := float_of_string_r (rev s).

*)
Definition isPositive (s: list ascii): (bool * (list ascii)) :=
  match s with
  | [] => (false, [])
  | h::t => match h with
            | "-"%char => (false, t)
            | _ => (true, s)
            end
  end.

Fixpoint split_at_dot (s buffer: list ascii): (list ascii * list ascii) :=
  match s with
  | [] => (buffer, [])
  | h::t => match h with
            | "."%char => (buffer, t)
            | _ => split_at_dot t (buffer++[h])
            end
  end.
(*
Open Scope nat_scope.
Definition decompose_float_string (s: list ascii)(a: nat): option (bool * float * float * nat) :=
  let (p, rest) := isPositive s in
  let split := split_at_dot rest [] in
  match (length (fst split)) <=? 5 with
  | false => None (*num_of_string causes stackoverflow*)
  | true => let first_nat_o := float_of_string_minor (fst split) in
            match first_nat_o with
            | Some first_nat => let second_nat_o := float_of_string_minor (firstn a (snd split)) in
                                match second_nat_o with
                                | Some second_nat => Some (p, first_nat, second_nat, length (firstn a (snd split)))
                                | None => None
                                end
            | None => None
            end
  end.

Open Scope float_scope.
Fixpoint exp (base: float)(exponent: nat): float :=
  match exponent with
  | O => 1
  | S n => base * exp base n
  end.
Fixpoint exp_neg (base: float)(exponent: nat): float :=
  match exponent with
  | O => 1
  | S n => exp_neg base n / base 
  end.

Definition decomposition_to_float (t: (bool * float * float * nat)) : float :=
  let sign := fst (fst (fst t)) in
  let mult := match sign with
             | true => 1
             | false => (-1)
             end in
  mult * (snd (fst (fst t)) + ((exp_neg 10 (snd t)) * snd (fst t))).

Definition float_of_string (a: nat)(s : list ascii): option float :=
  let ir := decompose_float_string s a in
  match ir with
  | None => None
  | Some t => Some (decomposition_to_float t)
  end.
*)

Open Scope R_scope.
Definition real_of_ascii (c: ascii) : option R :=
 match c with
(* Zero is 0011 0000 *)
   | Ascii false false false false true true false false => Some 0
(* One is 0011 0001 *)
   | Ascii true false false false true true false false => Some 1
(* Two is 0011 0010 *)
   | Ascii false true false false true true false false => Some 2
   | Ascii true true false false true true false false => Some 3
   | Ascii false false true false true true false false => Some 4
   | Ascii true false true false true true false false => Some 5
   | Ascii false true true false true true false false => Some 6
   | Ascii true true true false true true false false => Some 7
   | Ascii false false false true true true false false => Some 8
   | Ascii true false false true true true false false => Some 9
   | _ => None
end.

Fixpoint real_of_string_r (s : list ascii) : option R :=
  match s with
  | [] => Some 0
  | h::t => match (real_of_ascii h), (real_of_string_r t) with
            | Some n, Some m => Some (n + 10 * m)
            | _ , _ => None
            end
  end.

Definition real_of_string_minor (s : list ascii): option R := real_of_string_r (rev s).

Close Scope nat_scope.
Close Scope string_scope.

Open Scope nat_scope.
Definition decompose_real_string (s: list ascii)(a: nat): option (bool * R * R * nat) :=
  let (p, rest) := isPositive s in
  let split := split_at_dot rest [] in
  match (length (fst split)) <=? 5 with
  | false => None (*num_of_string causes stackoverflow*)
  | true => let first_nat_o := real_of_string_minor (fst split) in
            match first_nat_o with
            | Some first_nat => let second_nat_o := real_of_string_minor (firstn a (snd split)) in
                                match second_nat_o with
                                | Some second_nat => Some (p, first_nat, second_nat, length (firstn a (snd split)))
                                | None => None
                                end
            | None => None
            end
  end.

Open Scope R_scope.
Fixpoint exp_R (base: R)(exponent: nat): R :=
  match exponent with
  | O => 1
  | S n => base * exp_R base n
  end.
Fixpoint exp_neg_R (base: R)(exponent: nat): R :=
  match exponent with
  | O => 1
  | S n => exp_neg_R base n / base 
  end.

Definition decomposition_to_real (t: (bool * R * R * nat)) : R :=
  let sign := fst (fst (fst t)) in
  let mult := match sign with
             | true => 1
             | false => (-1)
             end in
  mult * (snd (fst (fst t)) + ((exp_neg_R 10 (snd t)) * snd (fst t))).

Definition real_of_string_variant (a: nat)(s : list ascii): option R :=
  let ir := decompose_real_string s a in
  match ir with
  | None => None
  | Some t => Some (decomposition_to_real t)
  end.

Definition real_of_string (s: string) : R :=
  match real_of_string_variant 10 (list_ascii_of_string s) with
  | Some r => r
  | None => 0
  end.
