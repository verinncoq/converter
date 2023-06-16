From Coq Require Import Bool.Bool.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
Open Scope string_scope.
From Coq Require Import Lists.List. Import ListNotations.


From CoqE2EAI Require Export string_tree.
From CoqE2EAI Require Export inb.
From CoqE2EAI Require Export eqb_la.
From CoqE2EAI Require Export theorems.

(*for prooving*)
From CoqE2EAI Require Export tokenizer.

(*
Helper for the parser. Builds the syntax tree, appending to 'built_tree'
should be initialized with depth=0 and after_colon=false
*)
Fixpoint parse_recursive (built_tree: tree) (todo_list: list (list ascii)) (depth: nat) (after_colon: bool) : tree :=
  match todo_list with
  | [] => built_tree (*nothing more todo, tree will be returned*)
  | (active_token::todo_list') =>
    match after_colon, active_token with
    | true, _ => (*append active_token and go one depth up*) 
      parse_recursive (append_at_end built_tree depth active_token) todo_list' (depth-1) false
    | _, ["{"%char] => (*append nothing but go one depth down*) 
      parse_recursive built_tree todo_list' (depth+1) false
    | _, ["}"%char] => (*append nothing but go one depth up*) 
      parse_recursive built_tree todo_list' (depth-1) false
    | _, [":"%char] => (*append nothing but go one depth down, also set after_colon to true*)
      parse_recursive built_tree todo_list' (depth+1) true
    | _, _ => (*append active_token and stay in depth*)
      parse_recursive (append_at_end built_tree depth active_token) todo_list' depth false
    end
  end.

(*
Parsing function. Takes a list of tokens and return a syntax tree
*)
Definition parse (l: list (list ascii)) : tree := parse_recursive (subtree (list_ascii_of_string "main") []) l 0 false.

(*for prooving*)
Definition is_delimiter_string (s: list ascii): bool :=
match s with
| ["{"%char] => true
| ["}"%char] => true
| [":"%char] => true
| _ => false
end.

Fixpoint cut_down_tree (t: tree): list (list ascii) :=
  match t with
  | leaf v => [v]
  | subtree v [] => [v]
  | subtree v c => [v]++(concat (map cut_down_tree c))
  end.

Definition no_special_characters (s: list ascii): bool := negb (isSpecialString s).

(*
unfinished proof. Says that when a tree gets cutted down to a list of list asciis,
  that its the same as its input, when special characters get removed

Theorem forest_cut_down: forall (l: list(list ascii)),
  filter no_special_characters (cut_down_tree (parse l)) = filter no_special_characters (l).
*)


Lemma In_parse_helper: forall (todo: list (list ascii)) (s: list ascii) (t: tree) (depth: nat) (after_colon: bool),
InTree s t = true -> InTree s (parse_recursive t todo depth after_colon) = true.
Proof. induction todo.
- intros. simpl. apply H.
- intros. destruct after_colon.
  + simpl. apply IHtodo. apply InTree_cons. apply H.
  + simpl. destruct a.
    * apply IHtodo. apply InTree_cons. apply H.
    * destruct a. destruct b.
      -- destruct b0.
         ++ destruct b1.
            ** apply IHtodo. apply InTree_cons. apply H.
            ** destruct b2.
               --- destruct b3.
                   +++ destruct b4.
                       *** destruct b5.
                           ---- destruct b6.
                                ++++ apply IHtodo. apply InTree_cons. apply H.
                                ++++ destruct a0.
                                     **** apply IHtodo. apply H.
                                     **** apply IHtodo. apply InTree_cons. apply H.
                           ---- apply IHtodo. apply InTree_cons. apply H.
                       *** apply IHtodo. apply InTree_cons. apply H.
                   +++ apply IHtodo. apply InTree_cons. apply H.
               --- apply IHtodo. apply InTree_cons. apply H.
         ++ destruct b1.
            ** destruct b2.
               --- destruct b3.
                   +++ destruct b4.
                       *** destruct b5.
                           ---- destruct b6.
                                ++++ apply IHtodo. apply InTree_cons. apply H.
                                ++++ destruct a0.
                                     **** apply IHtodo. apply H.
                                     **** apply IHtodo. apply InTree_cons. apply H.
                           ---- apply IHtodo. apply InTree_cons. apply H.
                       *** apply IHtodo. apply InTree_cons. apply H.
                   +++ apply IHtodo. apply InTree_cons. apply H.
               --- apply IHtodo. apply InTree_cons. apply H.
            ** apply IHtodo. apply InTree_cons. apply H.
      -- destruct b0.
         ++ destruct b1.
            ** apply IHtodo. apply InTree_cons. apply H.
            ** destruct b2.
               --- destruct b3.
                   +++ destruct b4.
                       *** destruct b5.
                           ---- destruct b6.
                                ++++ apply IHtodo. apply InTree_cons. apply H.
                                ++++ destruct a0.
                                     **** apply IHtodo. apply InTree_cons. apply H.
                                     **** apply IHtodo. apply InTree_cons. apply H.
                           ---- destruct b6.
                                ++++ apply IHtodo. apply InTree_cons. apply H.
                                ++++ destruct a0.
                                     **** apply IHtodo. apply H.
                                     **** apply IHtodo. apply InTree_cons. apply H.
                       *** apply IHtodo. apply InTree_cons. apply H.
                   +++ apply IHtodo. apply InTree_cons. apply H.
               --- apply IHtodo. apply InTree_cons. apply H.
         ++ apply IHtodo. apply InTree_cons. apply H.
Qed.

Lemma In_parse_helper3: forall (s a: list ascii) (t: tree) (todo: list (list ascii)) (depth: nat) (after_colon: bool),
InTree s t || Inb todo s =
InTree s (parse_recursive t todo depth after_colon).
Proof. intros. induction todo.
- simpl. rewrite orb_false_r. reflexivity.
- simpl. rewrite <- orb_lazy_alt. rewrite orb_assoc. rewrite orb_comm. rewrite orb_assoc. rewrite orb_comm in IHtodo. 
  rewrite IHtodo. destruct after_colon.
  + Abort.

Lemma In_parse_helper2: forall (s a: list ascii) (t: tree) (todo: list (list ascii)) (d1 d2 d3: nat) (after_colon: bool),
InTree s (parse_recursive t todo d1 after_colon) = true ->
InTree s (parse_recursive (append_at_end t d2 a) todo d3 after_colon) = true.
Proof. intros. induction todo.
- simpl. simpl in H. apply InTree_cons. apply H. 
- Abort. 

Lemma In_parse_recursive: forall (todo: list (list ascii)) (s: list ascii) (t: tree) (depth: nat) (after_colon: bool),
Inb todo s = true /\ is_delimiter_string s = false -> InTree s (parse_recursive t todo depth after_colon) = true.
Proof. induction todo.
- intros. destruct H. simpl in H. discriminate.
- intros. destruct H. unfold parse. destruct (string_of_list_ascii a =? string_of_list_ascii s) eqn:E0.
  + apply sol_eq in E0. rewrite <- E0 in H0. destruct (eqb (string_of_list_ascii a) (string_of_list_ascii ["{"%char])) eqn:G1.
    * apply sol_eq in G1. rewrite G1 in H0. simpl in H0. simpl. discriminate.
    * destruct (eqb (string_of_list_ascii a) (string_of_list_ascii ["}"%char])) eqn:G2.
      -- apply sol_eq in G2. rewrite G2 in H0. simpl in H0. discriminate.
      -- destruct (eqb (string_of_list_ascii a) (string_of_list_ascii [":"%char])) eqn:G3.
         ++ apply sol_eq in G3. rewrite G3 in H0. simpl in H0. discriminate.
         ++ apply sol_neq in G1,G2,G3. simpl. destruct a eqn:A.
            ** destruct after_colon.
               --- apply In_parse_helper. rewrite E0. apply InTree_eq.
               --- apply In_parse_helper. rewrite E0. apply InTree_eq.
            ** destruct after_colon.
               --- apply In_parse_helper. rewrite E0. apply InTree_eq.
               --- destruct a0. destruct b.
                   +++ destruct b0.
                       *** destruct b1.
                           ---- apply In_parse_helper. rewrite E0. apply InTree_eq.
                           ---- destruct b2.
                                ++++ destruct b3.
                                     **** destruct b4.
                                          ----- destruct b5.
                                                +++++ destruct b6.
                                                      ***** apply In_parse_helper. rewrite E0. apply InTree_eq.
                                                      ***** destruct l.
                                                            ------ unfold not in G1. congruence.
                                                            ------ apply In_parse_helper. rewrite E0. apply InTree_eq.
                                                +++++ apply In_parse_helper. rewrite E0. apply InTree_eq.
                                          ----- apply In_parse_helper. rewrite E0. apply InTree_eq.
                                     **** apply In_parse_helper. rewrite E0. apply InTree_eq.
                                ++++ apply In_parse_helper. rewrite E0. apply InTree_eq.
                      *** destruct b1.
                           ---- destruct b2.
                                ++++ destruct b3.
                                     **** destruct b4.
                                          ----- destruct b5.
                                                +++++ destruct b6.
                                                      ***** apply In_parse_helper. rewrite E0. apply InTree_eq.
                                                      ***** destruct l.
                                                            ------ unfold not in G1. congruence.
                                                            ------ apply In_parse_helper. rewrite E0. apply InTree_eq.
                                                +++++ apply In_parse_helper. rewrite E0. apply InTree_eq.
                                          ----- apply In_parse_helper. rewrite E0. apply InTree_eq.
                                     **** apply In_parse_helper. rewrite E0. apply InTree_eq.
                                ++++ apply In_parse_helper. rewrite E0. apply InTree_eq.
                           ---- apply In_parse_helper. rewrite E0. apply InTree_eq.
                   +++ destruct b0.
                       *** destruct b1.
                           ---- apply In_parse_helper. rewrite E0. apply InTree_eq.
                           ---- destruct b2.
                                ++++ destruct b3.
                                     **** destruct b4.
                                          ----- destruct b5.
                                                +++++ apply In_parse_helper. rewrite E0. apply InTree_eq.
                                                +++++ destruct b6.
                                                      ***** apply In_parse_helper. rewrite E0. apply InTree_eq.
                                                      ***** destruct l.
                                                            ------ unfold not in G1. congruence.
                                                            ------ apply In_parse_helper. rewrite E0. apply InTree_eq.
                                          ----- apply In_parse_helper. rewrite E0. apply InTree_eq.
                                     **** apply In_parse_helper. rewrite E0. apply InTree_eq.
                                ++++ apply In_parse_helper. rewrite E0. apply InTree_eq.
                      *** destruct b1.
                           ---- destruct b2.
                                ++++ destruct b3.
                                     **** destruct b4.
                                          ----- destruct b5.
                                                +++++ apply In_parse_helper. rewrite E0. apply InTree_eq.
                                                +++++ apply In_parse_helper. rewrite E0. apply InTree_eq.
                                          ----- apply In_parse_helper. rewrite E0. apply InTree_eq.
                                     **** apply In_parse_helper. rewrite E0. apply InTree_eq.
                                ++++ apply In_parse_helper. rewrite E0. apply InTree_eq.
                           ---- apply In_parse_helper. rewrite E0. apply InTree_eq.
  + simpl. destruct after_colon.
    * apply IHtodo. split.
      -- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
         ++ rewrite H in E0. apply sol_neq in E0. congruence.
         ++ apply In_is_true_implies_Inb_is_true. apply H.
      -- apply H0.
    * destruct a.
      -- apply IHtodo. split.
         ++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
            ** rewrite H in E0. apply sol_neq in E0. congruence.
            ** apply In_is_true_implies_Inb_is_true. apply H.
         ++ apply H0.
      -- destruct a. destruct b.
         ++ destruct b0.
            ** destruct b1.
               --- apply IHtodo. split.
                   +++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                       *** apply sol_neq in E0. rewrite H in E0. congruence.
                       *** apply In_is_true_implies_Inb_is_true. apply H.
                   +++ apply H0.
               --- destruct b2.
                   +++ destruct b3.
                       *** destruct b4.
                           ---- destruct b5.
                                ++++ destruct b6.
                                     **** apply IHtodo. split.
                                          ----- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                +++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                                +++++ apply In_is_true_implies_Inb_is_true. apply H.
                                          ----- apply H0.
                                     **** destruct a0.
                                          ----- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                +++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                                +++++ apply IHtodo. split.
                                                      ***** apply In_is_true_implies_Inb_is_true. apply H.
                                                      ***** apply H0.
                                          ----- apply IHtodo. split.
                                                +++++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                      ***** apply sol_neq in E0. rewrite H in E0. congruence.
                                                      ***** apply In_is_true_implies_Inb_is_true. apply H.
                                                +++++ apply H0.
                                ++++ apply IHtodo. split.
                                     **** apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                          ----- apply sol_neq in E0. rewrite H in E0. congruence.
                                          ----- apply In_is_true_implies_Inb_is_true. apply H.
                                     **** apply H0.
                           ---- apply IHtodo. split.
                                ++++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                     **** apply sol_neq in E0. rewrite H in E0. congruence.
                                     **** apply In_is_true_implies_Inb_is_true. apply H.
                                ++++ apply H0.
                       *** apply IHtodo. split.
                           ---- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                ++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                ++++ apply In_is_true_implies_Inb_is_true. apply H.
                           ---- apply H0.
                   +++ apply IHtodo. split.
                       *** apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                           ---- apply sol_neq in E0. rewrite H in E0. congruence.
                           ---- apply In_is_true_implies_Inb_is_true. apply H.
                       *** apply H0.
            ** destruct b1.
               --- destruct b2.
                   +++ destruct b3.
                       *** destruct b4.
                           ---- destruct b5.
                                ++++ destruct b6.
                                     **** apply IHtodo. split.
                                          ----- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                +++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                                +++++ apply In_is_true_implies_Inb_is_true. apply H.
                                          ----- apply H0.
                                     **** destruct a0.
                                          ----- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                +++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                                +++++ apply IHtodo. split.
                                                      ***** apply In_is_true_implies_Inb_is_true. apply H.
                                                      ***** apply H0.
                                          ----- apply IHtodo. split.
                                                +++++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                      ***** apply sol_neq in E0. rewrite H in E0. congruence.
                                                      ***** apply In_is_true_implies_Inb_is_true. apply H.
                                                +++++ apply H0.
                                ++++ apply IHtodo. split.
                                     **** apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                          ----- apply sol_neq in E0. rewrite H in E0. congruence.
                                          ----- apply In_is_true_implies_Inb_is_true. apply H.
                                     **** apply H0.
                           ---- apply IHtodo. split.
                                ++++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                     **** apply sol_neq in E0. rewrite H in E0. congruence.
                                     **** apply In_is_true_implies_Inb_is_true. apply H.
                                ++++ apply H0.
                       *** apply IHtodo. split.
                           ---- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                ++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                ++++ apply In_is_true_implies_Inb_is_true. apply H.
                           ---- apply H0.
                   +++ apply IHtodo. split.
                       *** apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                           ---- apply sol_neq in E0. rewrite H in E0. congruence.
                           ---- apply In_is_true_implies_Inb_is_true. apply H.
                       *** apply H0.
               --- apply IHtodo. split.
                   +++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                       *** apply sol_neq in E0. rewrite H in E0. congruence.
                       *** apply In_is_true_implies_Inb_is_true. apply H.
                   +++ apply H0.
         ++ destruct b0.
            ** destruct b1.
               --- apply IHtodo. split.
                   +++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                       *** apply sol_neq in E0. rewrite H in E0. congruence.
                       *** apply In_is_true_implies_Inb_is_true. apply H.
                   +++ apply H0.
               --- destruct b2.
                   +++ destruct b3.
                       *** destruct b4.
                           ---- destruct b5.
                                ++++ apply IHtodo. split.
                                     **** apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                          ----- apply sol_neq in E0. rewrite H in E0. congruence.
                                          ----- apply In_is_true_implies_Inb_is_true. apply H.
                                     **** apply H0.
                                ++++ destruct b6.
                                     **** apply IHtodo. split.
                                          ----- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                +++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                                +++++ apply In_is_true_implies_Inb_is_true. apply H.
                                          ----- apply H0.
                                     **** destruct a0.
                                          ----- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                +++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                                +++++ apply IHtodo. split.
                                                      ***** apply In_is_true_implies_Inb_is_true. apply H.
                                                      ***** apply H0.
                                          ----- apply IHtodo. split.
                                                +++++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                      ***** apply sol_neq in E0. rewrite H in E0. congruence.
                                                      ***** apply In_is_true_implies_Inb_is_true. apply H.
                                                +++++ apply H0.
                           ---- apply IHtodo. split.
                                ++++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                     **** apply sol_neq in E0. rewrite H in E0. congruence.
                                     **** apply In_is_true_implies_Inb_is_true. apply H.
                                ++++ apply H0.
                       *** apply IHtodo. split.
                           ---- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                ++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                ++++ apply In_is_true_implies_Inb_is_true. apply H.
                           ---- apply H0.
                   +++ apply IHtodo. split.
                       *** apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                           ---- apply sol_neq in E0. rewrite H in E0. congruence.
                           ---- apply In_is_true_implies_Inb_is_true. apply H.
                       *** apply H0.
            ** destruct b1.
               --- destruct b2.
                   +++ destruct b3.
                       *** destruct b4.
                           ---- destruct b5.
                                ++++ destruct b6.
                                     **** apply IHtodo. split.
                                          ----- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                +++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                                +++++ apply In_is_true_implies_Inb_is_true. apply H.
                                          ----- apply H0.
                                     **** destruct a0.
                                          ----- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                +++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                                +++++ apply IHtodo. split.
                                                      ***** apply In_is_true_implies_Inb_is_true. apply H.
                                                      ***** apply H0.
                                          ----- apply IHtodo. split.
                                                +++++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                                      ***** apply sol_neq in E0. rewrite H in E0. congruence.
                                                      ***** apply In_is_true_implies_Inb_is_true. apply H.
                                                +++++ apply H0.
                                ++++ apply IHtodo. split.
                                     **** apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                          ----- apply sol_neq in E0. rewrite H in E0. congruence.
                                          ----- apply In_is_true_implies_Inb_is_true. apply H.
                                     **** apply H0.
                           ---- apply IHtodo. split.
                                ++++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                     **** apply sol_neq in E0. rewrite H in E0. congruence.
                                     **** apply In_is_true_implies_Inb_is_true. apply H.
                                ++++ apply H0.
                       *** apply IHtodo. split.
                           ---- apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                                ++++ apply sol_neq in E0. rewrite H in E0. congruence.
                                ++++ apply In_is_true_implies_Inb_is_true. apply H.
                           ---- apply H0.
                   +++ apply IHtodo. split.
                       *** apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                           ---- apply sol_neq in E0. rewrite H in E0. congruence.
                           ---- apply In_is_true_implies_Inb_is_true. apply H.
                       *** apply H0.
               --- apply IHtodo. split.
                   +++ apply Inb_is_true_implies_In_is_true in H. apply in_inv in H. destruct H.
                       *** apply sol_neq in E0. rewrite H in E0. congruence.
                       *** apply In_is_true_implies_Inb_is_true. apply H.
                   +++ apply H0.
Qed.

Theorem In_parser: forall (s: list ascii) (t: list (list ascii)),
Inb t s = true /\ is_delimiter_string s = false -> InTree s (parse t) = true.
Proof. intros. unfold parse. apply In_parse_recursive. apply H. Qed. 
