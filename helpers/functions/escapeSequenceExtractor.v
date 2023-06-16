From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export error_option.

(*a type for only escape sequences from C*)
Inductive EscapeSequence :=
  | Backslash: EscapeSequence
  | SingleQuote: EscapeSequence
  | DoubleQuote: EscapeSequence
  | BEL: EscapeSequence
  | BS: EscapeSequence
  | FF: EscapeSequence
  | LF: EscapeSequence
  | CR: EscapeSequence
  | TAB: EscapeSequence
  | VT: EscapeSequence
  | Octal: ascii -> ascii -> ascii -> EscapeSequence
  | Hex: ascii -> ascii -> EscapeSequence
  .

(*a type similar to char, with the extension for escape sequences*)
Inductive Character :=
  | Regular: ascii -> Character
  | Escape: EscapeSequence -> Character
  .

(*returns true if given char is a backslash*)
Definition isBackslash (c: ascii) : bool :=
  let n := nat_of_ascii c in n =? 92.

(*
Converts a list of chars into a list of (option) Characters. Detects escape sequences and handles them.
If there are Errors in the output list, this means that an escape sequence has an illegal format.
source for conversion: https://docs.python.org/3/reference/lexical_analysis.html#strings
*)
Fixpoint detect_escape_sequence (s: list ascii) : list (error_option Character) :=
  match s with
  | [] => []
  | h::t => match isBackslash h with
            | false => (Success (Regular h))::(detect_escape_sequence t)
            | true => match t with
                      | [] => [Error "A backslash (starting an escape sequence) was the last symbol of the line, holding no information. "]
                      | h'::t' => match h' with
                                  | "\"%char => (Success (Escape Backslash))::(detect_escape_sequence t')
                                  | "'"%char => (Success (Escape SingleQuote))::(detect_escape_sequence t')
                                  | """"%char => (Success (Escape DoubleQuote))::(detect_escape_sequence t')
                                  | "a"%char => (Success (Escape BEL))::(detect_escape_sequence t')
                                  | "b"%char => (Success (Escape BS))::(detect_escape_sequence t')
                                  | "f"%char => (Success (Escape FF))::(detect_escape_sequence t')
                                  | "n"%char => (Success (Escape LF))::(detect_escape_sequence t')
                                  | "r"%char => (Success (Escape CR))::(detect_escape_sequence t')
                                  | "t"%char => (Success (Escape TAB))::(detect_escape_sequence t')
                                  | "v"%char => (Success (Escape VT))::(detect_escape_sequence t')
                                  | "x"%char => (*must be hex value hh, expecting at least two more asciis*)
                                                match t' with
                                                | first::second::rest => (Success (Escape (Hex first second)))::(detect_escape_sequence rest)
                                                | _ => [Error "A \x needs at least two following characters representing the hexadecimal number."]
                                                end
                                  | _ => (*must be octal value ooo, expecting at least two more asciis*)
                                         match t' with
                                         | first::second::rest => (Success (Escape (Octal h' first second)))::(detect_escape_sequence rest)
                                         | _ => [Error "A backslash that indicated an octal number needs at least three following characters representing the octal number."]
                                         end
                                  end
                      end
            end
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

(*
source: https://stackoverflow.com/questions/15334909/convert-function-from-string-to-nat-in-coq
Converts an ascii into a nat. Examples:
"5"%char => Success 5%nat
"1"%char => Success 1%nat
"f"%char => Error
*)
Definition nat_of_ascii (c: ascii) : error_option nat :=
 match c with
(* Zero is 0011 0000 *)
   | Ascii false false false false true true false false => Success 0
(* One is 0011 0001 *)
   | Ascii true false false false true true false false => Success 1
(* Two is 0011 0010 *)
   | Ascii false true false false true true false false => Success 2
   | Ascii true true false false true true false false => Success 3
   | Ascii false false true false true true false false => Success 4
   | Ascii true false true false true true false false => Success 5
   | Ascii false true true false true true false false => Success 6
   | Ascii true true true false true true false false => Success 7
   | Ascii false false false true true true false false => Success 8
   | Ascii true false false true true true false false => Success 9
   | _ => Error "nat_of_asscii: found an ascii that does not represent a digit."
end.


(*Computes ascii of 3 octal digits. First digit must be 0,1,2 or 3, second and third must be 0,1,2,3,4,5,6 or 7.*)
Definition ascii_of_octal (o1 o2 o3: ascii) : error_option ascii :=
  match nat_of_ascii o1 with
  | Error e => Error e
  | Success n1 => match (0 <=? n1) && (n1 <=? 3) with
               | false => Error "Octal: first digit must be between 0 and 3."
               | true => match nat_of_ascii o2 with
                         | Error e => Error e
                         | Success n2 => match (0 <=? n2) && (n2 <=? 7) with
                                      | false => Error "Octal: second digit must be between 0 and 7."
                                      | true => match nat_of_ascii o3 with
                                                | Error e => Error e
                                                | Success n3 => match (0 <=? n3) && (n3 <=? 7) with
                                                             | false => Error "Octal: third digit must be between 0 and 7."
                                                             | true => Success (ascii_of_nat (64*n1 + 8*n2 + n3))
                                                             end
                                                end
                                      end
                         end
               end
  end.

From Coq Require Import Strings.HexString.
From Coq Require Import NArith.BinNatDef.

(*Computes ascii of 2 hex digits. Both digits must be 0,1,2,3,4,5,6,7,8,9,A,B,C,D,E or F. (lowercase is also allowed)*)
Definition ascii_of_hex (h1 h2: ascii) : error_option ascii :=
  match ascii_to_digit h1 with
  | None => Error "ascii_of_hex: found an ascii that does not represent a hex-digit."
  | Some n1 => match ascii_to_digit h2 with
               | None => Error "ascii_of_hex: found an ascii that does not represent a hex-digit."
               | Some n2 => Success (ascii_of_nat (16*(N.to_nat n1) + (N.to_nat n2)))
               end
  end.

(*Converts a character into an ascii (i.e. the escape sequences are handled, so that every combination of ascii can be created)*)
Definition ascii_of_character (c: Character) : error_option ascii :=
  match c with
  | Regular a => Success a
  | Escape seq => match seq with
                  | Backslash => Success "\"%char
                  | SingleQuote => Success "'"%char
                  | DoubleQuote => Success """"%char
                  | BEL => Success (ascii_of_nat 7 )
                  | BS  => Success (ascii_of_nat 8 )
                  | FF  => Success (ascii_of_nat 12)
                  | LF  => Success (ascii_of_nat 10)
                  | CR  => Success (ascii_of_nat 13)
                  | TAB => Success (ascii_of_nat 9 )
                  | VT  => Success (ascii_of_nat 11)
                  | Octal o1 o2 o3 => ascii_of_octal o1 o2 o3
                  | Hex h1 h2 => ascii_of_hex h1 h2
                  end
  end.

(*main function of the module. Converts escape sequences.*)
Definition escapeSequenceExtractor (l: list ascii) : error_option (list ascii) :=
  match list_error_option_to_error_option_list (detect_escape_sequence l) with
  | Error e => Error e
  | Success charlist => list_error_option_to_error_option_list (map ascii_of_character charlist)
  end.

