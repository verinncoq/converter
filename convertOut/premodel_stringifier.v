From Coq Require Import Ascii.
From Coq Require Import String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Arith.

From CoqE2EAI Require Export intermediate_representation.
From CoqE2EAI Require Export string_to_number.

Open Scope char_scope.
(*
computes +1 for input (which is ascii)
returns Some (overflow, enlarged ascii) if successfull
returns None else*)
Definition enlargeAsciiByOne (a: ascii) : option (bool * ascii) :=
  match a with
  | "0" => Some (false, "1")
  | "1" => Some (false, "2")
  | "2" => Some (false, "3")
  | "3" => Some (false, "4")
  | "4" => Some (false, "5")
  | "5" => Some (false, "6")
  | "6" => Some (false, "7")
  | "7" => Some (false, "8")
  | "8" => Some (false, "9")
  | "9" => Some (true, "0")
  | _ => None
  end.

(*computes +1 for input
input is list ascii (string), but the number is represented in reversed order (147 is 741)
output is also in reversed order
example: (enlargeFlippedStringNumberByOneRec 741) = 841*)
Fixpoint enlargeFlippedStringNumberByOneRec (s: list ascii) : list ascii :=
  match s with
  | [] => list_ascii_of_string "1"
  | h::t => match enlargeAsciiByOne h with
            | Some (overflow, a) => match overflow with
                                   | false => a :: t
                                   | true => a :: (enlargeFlippedStringNumberByOneRec t)
                                   end
            | None => list_ascii_of_string "NaN"
            end
  end.

(*computes +1 for input
input is string which represents a number
output is that string with one more
examples: 
(enlargeStringNumberByOne 741) = 742
(enlargeStringNumberByOne 2) = 3
(enlargeStringNumberByOne 9) = 10
*)
Definition enlargeStringNumberByOne (s: string) : string :=
  string_of_list_ascii (rev (enlargeFlippedStringNumberByOneRec (rev (list_ascii_of_string s)))).

(*converts nat to string*)
Fixpoint stringifyNat (n: nat) : string :=
  match n with
  | O => "0"
  | S n => enlargeStringNumberByOne (stringifyNat n)
  end.



(*x and y are fixed*)
Definition strigifyFunction_NatNatString_recXY (f: nat -> nat -> string) (x y: nat) : string :=
  "| " ++ (stringifyNat x) ++ ", " ++ (stringifyNat y) ++ " => real_of_string """ ++ (f x y) ++ """%string
  ".

(*x is fixed*)
Definition strigifyFunction_NatString_recX (f: nat -> string) (x: nat) : string :=
  "| " ++ (stringifyNat x) ++ " => real_of_string """ ++ (f x) ++ """%string
  ".

(*x is fixed*)
Fixpoint strigifyFunction_NatNatString_recY (f: nat -> nat -> string) (x y: nat) : string :=
  match y with
  | O => strigifyFunction_NatNatString_recXY f x y
  | S ylower => strigifyFunction_NatNatString_recXY f x y ++ strigifyFunction_NatNatString_recY f x ylower
  end.

(*y is fixed*)
Fixpoint strigifyFunction_NatNatString_recX (f: nat -> nat -> string) (x y: nat) : string :=
  match x with
  | O => strigifyFunction_NatNatString_recY f x y ++ "| _, _ => real_of_string ""0.0""%string
  "
  | S xlower => strigifyFunction_NatNatString_recY f x y ++ strigifyFunction_NatNatString_recX f xlower y
  end.

Fixpoint strigifyFunction_NatString_rec (f: nat -> string) (x: nat) : string :=
  match x with
  | O => strigifyFunction_NatString_recX f x ++ "| _ => real_of_string ""0.0""%string
  "
  | S xlower => strigifyFunction_NatString_recX f x ++ strigifyFunction_NatString_rec f xlower
  end.

(*turns a function nat -> nat -> string into a string for file-output, processes first x and y nats*)
Definition strigifyFunction_NatNatString (f: nat -> nat -> string) (x y: nat) : string :=
  "(fun x y: nat =>
   match x, y with
  "++
  strigifyFunction_NatNatString_recX f (x-1) (x-1) ++
  "end)
  ".

(*turns a function nat -> string into a string for file-output, processes first x nats*)
Definition strigifyFunction_NatString (f: nat -> string) (x: nat) : string :=
  "(fun x: nat =>
   match x with
  "++
  strigifyFunction_NatString_rec f (x-1) ++
  "end)
  ".

(*gets a string and an ascii and another string, replaces all occurrences of a with s*)
Fixpoint replace (s: string) (a: ascii) (r: string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => match Ascii.eqb c a with
                     | true => r ++ (replace rest a r)
                     | false => String c (replace rest a r)
                     end
  end.

Open Scope string_scope.
(*gets a string and a string and another string, replaces the first occurrence of s1 with s2*)
Fixpoint replaceString (s: string) (s1: string) (s2: string) : string :=
  let len := String.length s1 in
  match s with
  | EmptyString => EmptyString
  | String c rest => match String.eqb s1 (substring 0 len s) with
                     | true => s2 ++ (substring len (String.length s) s)
                     | false => String c (replaceString rest s1 s2)
                     end
  end.

(*gets a string and an ascii, removes all occurrences of a*)
Fixpoint remove (s: string) (a: ascii) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => match Ascii.eqb c a with
                     | true => remove rest a
                     | false => String c (remove rest a)
                     end
  end.

(*makes a valid name out of a string, so it can be used as a variable name in coq*)
Definition makeName (s: string) :=
  replace (
    replace (
      replace (
        replace (
          replace (
            replace (
              replace (
                replace (
                  replace (
                    replace (
                      remove (
                        remove (
                          remove (
                            remove s """"
                          ) "'"
                        ) "."
                      ) ":"
                    ) "0" "_zero_"
                  ) "1" "_one_"
                ) "2" "_two_"
              ) "3" "_three_"
            ) "4" "_four_"
          ) "5" "_five_"
        ) "6" "_six_"
      ) "7" "_seven_"
    ) "8" "_eight_"
  ) "9" "_nine_".



Open Scope string_scope.
(*converts every NNPremodel node (except for output) into a string for file-output*)
Definition stringifyNNPremodel (nnseq: NNPremodel) : string :=
  match nnseq with
  | NNPremodel_initializer_matrix name n m function => 
    "Definition " ++ (makeName name) ++ " := mk_matrix " ++ (stringifyNat m) ++ " " ++ (stringifyNat n) ++ " " ++ strigifyFunction_NatNatString function m n ++ "."
  | NNPremodel_initializer_vector name n function =>
    "Definition " ++ (makeName name) ++ " := mk_colvec " ++ (stringifyNat n) ++ " " ++ strigifyFunction_NatString function n ++ "."
  | NNPremodel_Output name dim =>
    ""
  | NNPremodel_Linear name next weight bias transB beta =>
    let weight_prefix := match transB with
                         | "0.0" => ""%string
                         | _ => "(transpose "%string
                         end in
    let weight_suffix := match transB with
                         | "0.0" => " "%string
                         | _ => ")"%string
                         end in
    let bias_prefix := match beta with
                         | "1.0" => ""%string
                         | _ => "(scalar_mult (real_of_string """ ++ beta ++ """) "
                         end in
    let bias_suffix := match beta with
                         | "1.0" => " "%string
                         | _ => ") "
                         end in
    "Definition " ++ (makeName name) ++ " := NNLinear " ++ weight_prefix ++ (makeName weight) ++ weight_suffix ++
    " " ++ bias_prefix ++ (makeName bias) ++ bias_suffix ++ (makeName next) ++ "."
  | NNPremodel_ReLu name next =>
    "Definition " ++ (makeName name) ++ " := NNReLU " ++ (makeName next) ++ "."
  end.

Definition isOutput (nnseq: NNPremodel) : bool :=
  match nnseq with
  | NNPremodel_Output _ _ => true
  | _ => false
  end.

(*returns an output nodes as pair with its name*)
Definition oneOutput (node: NNPremodel) : (string * string) :=
  match node with
  | NNPremodel_Output name dim => ((makeName name), "(NNOutput (output_dim:=" ++ (stringifyNat dim) ++ "))")
  | _ => ("Error: non-output node found in only-output list, meaning installation is broken", "")
  end.

(*returns all output nodes as pairs with their names*)
Definition allOutputs (nodelist: list NNPremodel) : list (string * string) :=
  map oneOutput (List.filter isOutput nodelist).

(*the first occurrence of every output node in the list gets renamend*)
Fixpoint addOutput (outputs: list (string * string)) (nnseq: string) : string :=
  match outputs with
  | [] => nnseq
  | (var_name, definition)::t => addOutput t (replaceString nnseq var_name definition)
  end.

(*master function. list of NNPremodel nodes gets converted into string for output*)
Definition premodel_stringifier (l: list NNPremodel) : string :=
  "(*this file was generated automatically*)
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.

From Coq Require Import Reals.
From Coquelicot Require Import Coquelicot.
From CoqE2EAI Require Import matrix_extensions piecewise_affine neuron_functions.
From CoqE2EAI Require Import neural_networks.
From CoqE2EAI Require Import string_to_number.
From CoqE2EAI Require Import transpose_mult_matrix.
  
Open Scope nat_scope.

" ++
    String.concat "

" (map (addOutput (allOutputs l)) (map stringifyNNPremodel l)).



(*PROOFS*)

Lemma nat_zeroeight: forall (s: string) (n: nat),
String.length s = 1 -> ((nat_of_string (list_ascii_of_string s)) = Some n -> stringifyNat n = s).
Proof. intros. induction s.
  - simpl in H. inversion H.
  - simpl in H. induction s.
    + simpl in H. simpl in H0. destruct a as [[|][|][|][|][|][|][|][|]];
      try unfold nat_of_string in H0; simpl in H0; inversion H0;
      simpl; unfold enlargeStringNumberByOne; simpl; reflexivity.
    + simpl in H. inversion H. Qed.


Lemma nat_ascii: forall (c: ascii) (n: nat),
nat_of_ascii c = Some n -> stringifyNat n = string_of_list_ascii [c].
Proof. intros. destruct c as [[|][|][|][|][|][|][|][|]];
  try simpl in H; inversion H; try simpl; unfold enlargeStringNumberByOne; simpl; reflexivity. Qed.


Lemma zerochar: forall (n: nat),
n = 0 -> stringifyNat n = "0".
Proof. intros. rewrite H. simpl. reflexivity. Qed.



(*
unfinished proofs

(*proof about nat and string*)
Theorem nat_string_nat: forall (n: nat), 
nat_of_string (list_ascii_of_string (stringifyNat n)) = Some n.
Proof. induction n. Abort.

(*TODO proof about nat and string*)
Theorem string_nat_string: forall (n m: nat),
nat_of_string (list_ascii_of_string (stringifyNat n)) = Some m -> n = m.
Proof. intros. induction n.
  - simpl in H. unfold nat_of_string in H. simpl in H. inversion H. reflexivity.
  - unfold stringifyNat in H. unfold en
*)