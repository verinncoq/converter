From Coq Require Import Bool.Bool.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.


(*Source: https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32) (* space *)
           (n =? 9)) (* tab *)
      (orb (n =? 10) (* linefeed *)
           (n =? 13)). (* Carriage return. *)

Definition isNotWhitespace (c: ascii): bool :=
  negb (isWhite c).

(*Following code is inspired by https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isQuotationMark (c: ascii) : bool :=
  let n := nat_of_ascii c in n =? 34.

(*Following code is inspired by https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isColon (c: ascii) : bool :=
  let n:= nat_of_ascii c in n =? 58.

(*Following code is inspired by https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isLeftBrace (c: ascii) : bool :=
  let n:= nat_of_ascii c in n =? 123.

(*Following code is inspired by https://softwarefoundations.cis.upenn.edu/lf-current/ImpParser.html*)
Definition isRightBrace (c: ascii) : bool :=
  let n:= nat_of_ascii c in n =? 125.

Fixpoint split_string (f: ascii->bool) (z s: list ascii): list (list ascii) :=
let revz := match z with [] => [] | _::_ => [rev z] end in
match s with
| [] => revz
| h::t => match f h with
  | true => (revz++[[h]])++(split_string f [] t)
  | false => (split_string f (h::z) t)
  end
end.

Fixpoint split_strings (f: ascii->bool) (s: list(list ascii)): list (list ascii) :=
match s with
| [] => []
| h::t => (split_string f [] h) ++ (split_strings f t)
end.

Fixpoint merge_quotationMark (inMarkZone: bool)(z: list ascii)(s: list(list ascii)): list(list ascii) :=
match s with
| [] => [z]
| h::t => match inMarkZone, existsb isQuotationMark h with
  | true, true => (z++h)::(merge_quotationMark false [] t)
  | true, false => merge_quotationMark true (z++h) t
  | false, true => merge_quotationMark true (z++h) t
  | false, false => (z++h)::merge_quotationMark false [] t
  end
end.

Definition NotEmpty (s: list ascii): bool :=
match s with
| [] => false
| _::_ => true
end.

Definition no_only_white (s: list ascii): bool :=
negb (forallb isWhite s).

Definition hasQuotationMark (s: list ascii): bool := existsb isQuotationMark s.

Definition hasColon (s: list ascii): bool := existsb isColon s.

Definition hasLeftBrace (s: list ascii): bool := existsb isLeftBrace s.

Definition hasRightBrace (s: list ascii): bool := existsb isRightBrace s.

Definition isSpecialString (s: list ascii): bool :=
orb 
  (orb 
    (hasQuotationMark s)
    (hasColon s)
  )
  (orb
    (hasLeftBrace s)
    (hasRightBrace s)
  )
.

(*
Tokenizer funktion. Takes a list ascii and returns a list of list ascii, containing the tokens
*)
Definition tokenizer (s: list ascii): list (list ascii) :=
  filter no_only_white (
    merge_quotationMark false [] (
      split_strings isQuotationMark (
        split_strings isRightBrace (
          split_strings isLeftBrace (
            split_strings isColon (
              split_string isWhite [] s
)))))).

(*for prooving*)
Fixpoint count_occ_string (s: list ascii)(a: ascii): nat :=
match s with
| [] => 0
| h::t =>
  match (eqb h a) with
  | true => 1 + count_occ_string t a
  | false => count_occ_string t a
  end
end.

(*for proving*)
Definition right_QuotationMark_count (s: list ascii) := even (count_occ_string s """"%char).

(*PROOFS*)
(*proof adapted from https://stackoverflow.com/questions/73026651/coq-implementation-of-splitstring-and-proof-that-nothing-gets-deleted*)
Lemma not_more_not_less_split_string_stronger: forall (f: ascii->bool)(z s: list ascii),
rev z ++ s = concat (split_string f z s).
Proof. intros f z s. revert z.
  induction s as [ | a s IHl]. 
  - simpl. destruct z.
    + reflexivity.
    + reflexivity.
  - simpl. case_eq (f a). intro Ha.
   + intros z. repeat rewrite concat_cons. destruct z.
      * simpl. now rewrite <- IHl.
      * simpl. now rewrite <- IHl.
   + intro buf. intros. rewrite <- IHl. cbn. now rewrite <- app_assoc. 
Qed.

Lemma not_more_not_less_split: forall (f: ascii->bool)(s: list ascii),
s = concat (split_string f [] s).
Proof. intros. apply not_more_not_less_split_string_stronger with (z:=[]). Qed.

Lemma not_more_not_less_split_strings: forall (f: ascii->bool)(s: list(list ascii)),
concat s = concat (split_strings f s).
Proof. intros f s. induction s.
- simpl. reflexivity.
- simpl. rewrite concat_app. rewrite <- not_more_not_less_split. rewrite <- IHs. simpl. reflexivity. Qed.

Lemma not_more_not_less_merge_quotationMark_even_stronger: forall (b: bool)(t: list ascii)(s: list (list ascii)),
t ++ concat s = concat (merge_quotationMark b t s).
Proof. intros. revert t b. induction s.
  - simpl. reflexivity.
  - simpl. destruct b eqn:B.
    * case_eq (existsb isQuotationMark a).
      + simpl. rewrite <- IHs. simpl. rewrite app_assoc. reflexivity.
      + rewrite <- IHs. rewrite app_assoc. reflexivity.
    * case_eq (existsb isQuotationMark a).
      + rewrite <- IHs. rewrite app_assoc. reflexivity.
      + simpl. rewrite <- IHs with (b:=false). simpl. rewrite app_assoc. reflexivity. Qed.

Lemma not_more_not_less_merge_quotationMark_stronger: forall (t: list ascii)(s: list (list ascii)),
t ++ concat s = concat (merge_quotationMark false t s).
Proof. intros s t. rewrite <- not_more_not_less_merge_quotationMark_even_stronger. reflexivity. Qed.

Lemma not_more_not_less_merge_quotationMark: forall (s: list (list ascii)),
concat s = concat (merge_quotationMark false [] s).
Proof. intros s. rewrite <- not_more_not_less_merge_quotationMark_stronger. simpl. reflexivity. Qed.

Lemma filter_no_white: forall (s: list ascii),
no_only_white s = false -> filter isNotWhitespace s = [].
Proof. intros s. induction s.
- simpl. reflexivity.
- destruct (isNotWhitespace a) eqn: W.
  * intros H. unfold no_only_white in H. unfold forallb in H.
    rewrite negb_andb in H. apply orb_false_iff in H. destruct H. 
    unfold isNotWhitespace in W. rewrite W in H. discriminate H.
  * unfold filter. destruct (isNotWhitespace a) eqn: W2.
    + discriminate.
    + unfold no_only_white. simpl. rewrite negb_andb. rewrite orb_false_iff. 
      intros H. destruct H. apply IHs. unfold no_only_white. apply H0. Qed.

Lemma double_filter_redundant: forall (s: list(list ascii)),
filter isNotWhitespace (concat s) = filter isNotWhitespace (concat (filter no_only_white s)).
Proof. intros s. induction s.
- simpl. reflexivity.
- simpl. destruct (no_only_white a) eqn:W.
  * simpl. rewrite filter_app. rewrite IHs. rewrite filter_app. reflexivity.
  * rewrite filter_app. apply filter_no_white in W. rewrite W. simpl. rewrite IHs. reflexivity. Qed.

Theorem not_less_not_more: forall (s: list ascii),
filter isNotWhitespace s = filter isNotWhitespace (concat (tokenizer s)).
Proof. intros s. unfold tokenizer. rewrite <- double_filter_redundant.
rewrite <- not_more_not_less_merge_quotationMark. rewrite <- not_more_not_less_split_strings.
rewrite <- not_more_not_less_split_strings. rewrite <- not_more_not_less_split_strings.
rewrite <- not_more_not_less_split_strings. rewrite <- not_more_not_less_split. reflexivity. Qed.

Lemma not_white_in_tokenized: forall(a: ascii) (s: list ascii),
isNotWhitespace a = true /\ In a s -> In a (concat (tokenizer s)).
Proof. intros. assert(Hf: In a (filter isNotWhitespace s)).
- apply filter_In. apply and_comm. apply H.
- rewrite not_less_not_more in Hf. apply filter_In in Hf. destruct Hf. apply H0. Qed.