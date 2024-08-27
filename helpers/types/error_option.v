From Coq Require Import Strings.String.

Set Implicit Arguments.

Inductive error_option (T: Type) : Type :=
  | Success: T -> error_option T
  | Error: string -> error_option T.

Arguments Success {T} t.
Arguments Error {T}.

Definition isSuccess {T: Type} (eo: error_option T) : bool :=
  match eo with
  | Success _ => true
  | Error _ => false
  end.

Definition isError {T: Type} (eo: error_option T) : bool :=
  negb (isSuccess eo).

Definition getValue {T: Type} (eo: error_option T) : option T :=
  match eo with
  | Success t => Some t
  | Error _ => None
  end.

Definition getError {T: Type} (eo: error_option T) : option string :=
  match eo with
  | Success _ => None
  | Error s => Some s
  end.

Definition error_option_compose {A B C: Type} (f: A -> error_option B) (g: B -> error_option C): A -> error_option C :=
  fun (x: A) => 
    match f x with
    | Success fx => g fx
    | Error s => Error s
    end.