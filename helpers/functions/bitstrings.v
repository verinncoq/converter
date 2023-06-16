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
From CoqE2EAI Require Export stringifyN.
From CoqE2EAI Require Export error_option.

(*bits are represented through bools, 0 equals false, 1 equals true*)
Definition bit_of_bool (b: bool) : ascii :=
  match b with
  | true => "1"
  | false => "0"
  end.

(*converts an ascii (which consists itself of 8 bits) into a string of length 8 consisting 0 and 1*)
Definition bitstring_of_ascii (a: ascii) : string :=
  match a with
  | Ascii a b c d e f g h => string_of_list_ascii (map bit_of_bool [h;g;f;e;d;c;b;a])
  end.

(*returns first four elements (or less) of l*)
Definition firstFour {T: Type} (l: list T) : list T :=
  match l with
  | [] => []
  | l1::[] => [l1]
  | l1::l2::[] => [l1; l2]
  | l1::l2::l3::[] => [l1; l2; l3]
  | l1::l2::l3::l4::t => [l1; l2; l3; l4]
  end.


(*switches 4 bytes in a row, converting a list of bitstring consisting of 32-Bit large data points from big-endian into little-endian, then concats bitstrings*)
Fixpoint little_endian (l: list string) : string :=
  let ff := firstFour l in
  match l with
  | [] => ""%string
  | h::[] => (String.concat ""%string (rev ff))
  | h1::h2::[] => (String.concat ""%string (rev ff))
  | h1::h2::h3::[] => (String.concat ""%string (rev ff))
  | h1::h2::h3::h4::t => (String.concat ""%string (rev ff)) ++ little_endian t
  end.

(*
Helper for binary_to_decimal.
Is called by that function.
Should not be called manually.
*)
Fixpoint binary_to_decimal_rec (bitstring: list bool) : nat :=
  match bitstring with
  | [] => 0
  | h::t => match h with
            | false => 2 * (binary_to_decimal_rec t)
            | true => 1 + (2 * (binary_to_decimal_rec t))
            end
  end.

(*
Converts a list of bools into a natural number. 
The input is interpreted as a binary natural number, where 0 equals false and 1 equals true.
*)
Definition binary_to_decimal (bitstring: list bool) : nat :=
  binary_to_decimal_rec (rev bitstring).

(*
If the input string consists only of 1 and 0, it gets converted into Success list of bools, where 0 equals false and 1 equals true.
Otherwise Error is returned.
*)
Fixpoint list_bool_of_string (s: string) : error_option (list bool) :=
  match s with
  | EmptyString => Success []
  | String c t => match list_bool_of_string t with
                  | Success l => match c with
                              | "0"%char => Success (false::l)
                              | "1"%char => Success (true::l)
                              | _ => Error "list_bool_of_string: string must contain either 0 or 1."
                              end
                  | Error e => Error e
                  end
  end.

(*
Converts a list of bools into a string, where 0 equals false and 1 equals true.
*)
Fixpoint string_of_list_bool (l: list bool) : string :=
  match l with
  | [] => EmptyString
  | h::t => match h with
            | true  => String "1"%char (string_of_list_bool t)
            | false => String "0"%char (string_of_list_bool t)
            end
  end.

(*counts all the dots in a string*)
Fixpoint count_dot (s: string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => match c with
                   | "."%char => 1 + count_dot s'
                   | _        =>     count_dot s'
                   end
  end.

Close Scope nat_scope.
Open Scope N_scope.

(*
Helper for binary_to_decimal_after_dot.
Is called by that function.
Should not be called manually.
*)
Fixpoint binary_to_decimal_after_dot_precise (l: list bool) (precision counter: N) : N := 
  match l with
  | []   => N0
  | h::t => match h with
            | true  => (N.div precision counter) + binary_to_decimal_after_dot_precise t precision (counter*2)
            | false =>                             binary_to_decimal_after_dot_precise t precision (counter*2)
            end
  end.

(*
Converts the part after the dot of a binary number into a natural number.
The output can be converted into a string, which then can be appended to the (decimal-converted) part before the dot of the binary number, along with a dot.
The binary number is represented as a list of bools, where 0 equals false and 1 equals true.
Examples:
11   =>   75  (because 10.11      => 2,75   )
1001 => 5625  (because 10101.1001 => 21,5625)
*)
Definition binary_to_decimal_after_dot (l: list bool) : N := binary_to_decimal_after_dot_precise (true::l) (10^(N.of_nat (length (true::l)))) 1.


Close Scope N_scope.
Open Scope nat_scope.
Open Scope string_scope.

(*removes first char if exists*)
Definition remove_first_char (s: string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => s'
  end.

(*Converts a binary number into a decimal number. The binary number might contain a dot, but must be positive!*)
Definition bin_to_dec (s: string) (n: nat) : error_option string :=
  match count_dot s with
  | 0 => match list_bool_of_string s with
         | Success l => Success (writeN n (N.of_nat (binary_to_decimal l)))
         | Error e => Error e
         end
  | 1 => let tuple := split_string_dot_second s in
         match list_bool_of_string (fst tuple) with
               | Success l => let firstnum := binary_to_decimal l in
                           match snd tuple with
                           | EmptyString => Error "internal error: no dot was found while counting one (bin_to_dec-function)" (*not dot, but cant be the case*)
                           | String c s  => (*dot must be in c*)
                                     match list_bool_of_string s with
                                     | Success l' => Success ((writeN n (N.of_nat firstnum)) ++ (String c (remove_first_char (writeN n (binary_to_decimal_after_dot l')))))
                                     | Error e => Error e
                                     end
                           end
               | Error e => Error e
               end
  | _ => Error "bin_to_dec: input string must contain zero or exaclty one dot."
  end.

(*Converts a binary number into a decimal number. The binary number might contain a dot and a sign.*)
Definition bin_to_dec_z (s: string) (n: nat) : error_option string :=
  match s with
  | String "-"%char rest => match bin_to_dec rest n with
                            | Error e => Error e
                            | Success dec => Success (String "-"%char dec)
                            end
  | _                    =>                  bin_to_dec s n
  end.