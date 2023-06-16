From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export unpack.
From CoqE2EAI Require Export error_option.
From CoqE2EAI Require Export stateful_map.

Open Scope nat_scope.

(*Source: https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isWhite (c : ascii) : bool :=
  let n := Ascii.nat_of_ascii c in
  orb (orb (n =? 32) (* space *)
           (n =? 9)) (* tab *)
      (orb (n =? 10) (* linefeed *)
           (n =? 13)). (* Carriage return. *)

(*Removes all white characters at the beginning of s.*)
Fixpoint removeWhitesAtBeginning (s: string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => match isWhite c with
                   | true  => removeWhitesAtBeginning s'
                   | false => s
                   end
  end.

Open Scope string_scope.
(*returns true if line contins raw_data field*)
Definition is_raw_data (s: string) : bool :=
  let raw_data_possible := substring 0 8 (removeWhitesAtBeginning s) in
  raw_data_possible =? "raw_data".

(*returns true if line contins data_type field*)
Definition is_data_type (s: string) : bool :=
  let data_type_possible := substring 0 9 (removeWhitesAtBeginning s) in
  data_type_possible =? "data_type".

(*Removes n chars (if possible) at the beginning of s.*)
Fixpoint remove_at_beginning (s: string) (n: nat) : string :=
  match n with
  | O    => s
  | S n' => match s with
           | EmptyString => s
           | String c s' => remove_at_beginning s' n'
           end
  end.

Definition reverse_string (s: string) : string :=
  string_of_list_ascii (rev (list_ascii_of_string s)).

(*Removes n chars (if possible) at the end of s.*)
Definition remove_at_end (s: string) (n: nat) : string :=
  reverse_string (remove_at_beginning (reverse_string s) n).

(*Returns the content of the raw_data field in a line.*)
Definition extract_raw_data (s: string) : string :=
  remove_at_end (remove_at_beginning (removeWhitesAtBeginning s) 11) 1.

(*Returns the content of the data_type field in a line.*)
Definition extract_data_type (s: string) : string :=
  remove_at_beginning (removeWhitesAtBeginning s) 11.

(*Adds a field to the converted data to make it readable for the tokenizer.*)
Definition rearrange_converted_data (s: string) : string :=
  ("data_converted: " ++ s) ++ "
  ".

(*Converts a line (with or without raw_data field) into data. It is interpreted as a float.*)
Definition convert_line (s: string) : error_option string :=
  match is_raw_data s with
  | false => Success s
  | true  => match (unpack_mult 300 (extract_raw_data s)) with
             | Error e => Error e
             | Success l => Success (String.concat "" (map rearrange_converted_data l))
             end
  end.

(*Converts a line (with or without raw_data field) into data, dependant on the state*)
Definition convert_line_given_datatype (datatype line: string) : error_option string :=
  match is_raw_data line with
  | true  => match datatype with
             | "None" => Error "Raw_data_converter: No datatype has been given. The 'data_type' field must be before the 'raw_data' field."
             | "1"    => (*float*) convert_line line
             | _      => Error ("Raw_data_converter: ONNX Datatype " ++ (datatype ++ " is currently not supported."))
             end
  | false => Success line
  end.

(*
Helper for split_lines.
Is called by that function.
Should not be called manually.
*)
Fixpoint split_lines_rec (s buf: string) : list string :=
  match s with
  | EmptyString => [buf]
  | String c s' => match c with
                   | "010"%char => buf::(split_lines_rec s' EmptyString) (*linefeed*)
                   | _          => split_lines_rec s' (buf ++ (String c EmptyString))
                   end
  end.

(*Splits a string by linefeed characters*)
Definition split_lines (s: string) : list string := split_lines_rec s EmptyString.

(*Computes next state depending on line and current state*)
Definition getState (state line: string) : string :=
  match is_data_type line with
  | true  => extract_data_type line (*get state from data_type field.*)
  | false => match is_raw_data line with
             | true  => "None" (*raw_data has been read, looking for new data_type field.*)
             | false => state (*no special line, keep state*)
             end
  end.

Definition raw_data_converter (s: list ascii) : error_option (list ascii) :=
  let lines := split_lines (string_of_list_ascii s) in
  let map_convertion := list_error_option_to_error_option_list (stateful_map lines "None" convert_line_given_datatype getState) in
  match map_convertion with
  | Error e => Error e
  | Success s => let seperator := String "010"%char EmptyString in (*linefeed*)
                 Success (list_ascii_of_string (String.concat seperator s))
  end.

Definition test := list_ascii_of_string "
  name: ""torch-jit-export""
  initializer {
    dims: 4
    dims: 4
    data_ty
    name: ""net.0.weight""
    raw_dsata: ""\340\232\241=[:\267\276$\205\350\277\246v\214\277\215=D\276\031zY\276\035&\032\277\340!\235\2758\242\016=x\021\347\275x\""\307=\002\026\311\274\342Z\205=\324\342;>w\032\344?\355m\242?""
  }
  initializer {
    dims: 4
    data_type: 1
    name: ""net.0.bias""
    raw_data: ""\207\3330?b\370-\276\333\210\370\275\337a\036?""
  }".

(*Compute getState "1" "data_type: bla".

Compute string_of_list_ascii (match (raw_data_converter test) with
                              | Success s => s
                              | Error s => list_ascii_of_string s end).
*)
