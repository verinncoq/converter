From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export error_option.

Open Scope list_scope.
(*
if a and b are success, a is appended to b. if not, first error is thrown
*)
Definition append_option {T: Type}(a: error_option T)(b: error_option (list T)) : error_option (list T) :=
  match a with
  | Error s => Error s
  | Success la => match b with
                    | Error s => Error s
                    | Success lb => Success (la::lb)
                    end
   end.

(*if there is no error in l, a list is returned, if there is some error in l, the first errormessage is returned*)
Fixpoint extract_error {T: Type}(l: list (error_option T)) : error_option (list T) :=
  match l with
  | [] => Success []
  | h::t => append_option h (extract_error t)
  end.


Lemma extract_error_length: forall {T: Type}(l: list (error_option T))(ol: list T),
  extract_error l = Success ol -> length ol = length l.
Proof. induction l.
  - intros. simpl in H. inversion H. reflexivity.
  - induction ol.
    + intros. simpl in H. destruct a.
      * simpl in H. destruct (extract_error l).
        -- inversion H.
        -- inversion H.
      * simpl in H. inversion H.
    + intros. simpl. f_equal. apply IHl. destruct a.
      * simpl in H. destruct (extract_error l).
        -- inversion H. reflexivity.
        -- inversion H.
      * simpl in H. inversion H. Qed.