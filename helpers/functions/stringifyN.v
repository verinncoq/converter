From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import BinNat.

(*
This module is inspired by http://poleiro.info/posts/2013-03-31-reading-and-writing-numbers-in-coq.html.
There, nat is converted to string.
Here, N is converted to string.
That's the only difference.
*)

(*inspired by http://poleiro.info/posts/2013-03-31-reading-and-writing-numbers-in-coq.html*)
Definition NToDigit (n : N) : ascii :=
  match n with
    | 0%N => "0"
    | 1%N => "1"
    | 2%N => "2"
    | 3%N => "3"
    | 4%N => "4"
    | 5%N => "5"
    | 6%N => "6"
    | 7%N => "7"
    | 8%N => "8"
    | _ => "9"
  end.

(*inspired by http://poleiro.info/posts/2013-03-31-reading-and-writing-numbers-in-coq.html*)
Fixpoint writeNAux (time: nat) (n : N) (acc : string) : string :=
  let acc' := String (NToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match N.div n 10 with
        | 0%N => acc'
        | n' => writeNAux time' n' acc'
      end
  end.

(*inspired by http://poleiro.info/posts/2013-03-31-reading-and-writing-numbers-in-coq.html*)
Definition writeN (depth: nat) (n : N) : string :=
  writeNAux depth n "".

(*up to 8-digit numbers work fine, larger numbers begin to cause problems, because of the time nat*)

(*TODO compute length of decimal representation*)
