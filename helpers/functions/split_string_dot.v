From Coq Require Import Strings.String.

(*find the first dot and split the string there, dot is in first string*)
Definition split_string_dot_first (s: string): (string * string) :=
  match index 0 "." s with
  | Some i => let l := String.length s in
              ((substring 0 (i+1) s), (substring (i+1) l s))
  | None   => (""%string, s)
  end.

(*find the first dot and split the string there, dot is in second string*)
Definition split_string_dot_second (s: string): (string * string) :=
  match index 0 "." s with
  | Some i => let l := String.length s in
              ((substring 0 i s), (substring i l s))
  | None   => (""%string, s)
  end.