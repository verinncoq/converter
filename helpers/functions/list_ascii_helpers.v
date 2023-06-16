From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope char_scope.
(*functions only for tracking the error from a previous module (raw_data converter)*)

(*checks if list a begins with list b*)
Fixpoint begins_with (a b: list ascii) : bool :=
  match b with
  | [] => true
  | hb::tb => match a with
              | [] => false
              | ha::ta => (ha =? hb) && (begins_with ta tb)
              end
  end.

(*removes first element of list (which is LF in case of error)*)
Definition remove_first (s: list ascii) : list ascii :=
  match s with
  | [] => []
  | h::t => t
  end.