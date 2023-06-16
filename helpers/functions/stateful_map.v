From Coq Require Import Lists.List. Import ListNotations.

Fixpoint stateful_map {T T' S: Type} (l: list T) (state: S) (f: S -> T -> T') (getState: S -> T -> S) : list T' :=
  match l with
  | []   => []
  | h::t => let next_state := getState state h in
            (f state h) :: (stateful_map t next_state f getState)
  end.

Definition testlist := [0;1;2;3;4;5;6].

Definition map_fun (b: bool) (n: nat) : nat :=
  match b with
  | true => n
  | false => n+1
  end.

Definition getState (b: bool) (n: nat) : bool := negb b.

(*Compute stateful_map testlist true map_fun getState.*)
