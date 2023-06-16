From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List.

(*file containing many useful theorems that are used multiple times*)

(*theorem from https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html*)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof. intros P Q. intros H1. unfold not. intros H2. intros H3. apply H1 in H3. apply H2 in H3. apply H3. Qed.

(*like in_inv from https://coq.inria.fr/library/Coq.Lists.List.html*)
Theorem in_inv_inv: forall (a b: string) (l:list string), (a = b \/ In b l ) -> In b (a :: l).
Proof. intros a b l. intros H. destruct H.
  - simpl. left. apply H.
  - simpl. right. apply H.
  Qed.

Theorem filter_true: forall (T: Type) (a: T) (l : list T) (f: T -> bool),
(f a = true) -> filter f (a::l) = a::filter f l.
Proof. intros T a l f. intros H. unfold filter. rewrite H. reflexivity. Qed.

Theorem filter_false: forall (T: Type) (a: T) (l : list T) (f: T -> bool),
(f a = false) -> filter f (a::l) = filter f l.
Proof. intros T a l f. intros H. unfold filter. rewrite H. reflexivity. Qed.

Theorem string_of_list_constructer: forall (s t:list ascii),
string_of_list_ascii s = string_of_list_ascii t -> s = t.
Proof. intros. rewrite <- list_ascii_of_string_of_list_ascii. rewrite <- H.
rewrite list_ascii_of_string_of_list_ascii. reflexivity. Qed.

Theorem list_of_string_constructer: forall (s t:string),
list_ascii_of_string s = list_ascii_of_string t -> s = t.
Proof. intros. rewrite <- string_of_list_ascii_of_string. rewrite <- H.
rewrite string_of_list_ascii_of_string. reflexivity. Qed.

Theorem map_fst: forall (T F: Type)(h: T)(t: list T)(f: T->F),
map f (h::t) = f(h)::(map f t).
Proof. intros. simpl. reflexivity. Qed.

Theorem filter_fst: forall (T F: Type)(h: T)(t: list T)(f: T->bool),
f(h) = true -> filter f (h::t) = h::(filter f t).
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Theorem add_zero: forall (n m: nat),
n + m = 0 -> n = 0.
Proof. intros. induction n.
  - reflexivity.
  - simpl in H. inversion H. Qed.

Theorem add_comm: forall (n m: nat),
n + m = m + n.
Proof. induction n.
  - induction m.
    + simpl. reflexivity.
    + simpl. rewrite <- IHm. simpl. reflexivity.
  - induction m.
    + simpl. rewrite IHn. simpl. reflexivity.
    + simpl. rewrite IHn. rewrite <- IHm. simpl. f_equal; f_equal. rewrite <- IHn with m. reflexivity. Qed.

Theorem add_len: forall {T: Type}(l1 l2: list T),
  length (l1 ++ l2) = length l1 + length l2.
Proof. intros. induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity. Qed.

Theorem nat_ass: forall (a b c: nat),
a + b + c = a + (b + c).
Proof. intros. induction a.
- simpl. reflexivity.
- simpl. rewrite IHa. reflexivity. Qed.

Theorem add_len4: forall {T: Type}(l1 l2 l3 l4: list T),
  length (l1 ++ (l2 ++ (l3 ++ l4))) = length l1 + length l2 + length l3 + length l4.
Proof. intros. repeat rewrite add_len. repeat rewrite nat_ass. reflexivity. Qed.

Theorem len_add: forall {T1 T2: Type}(l11 l21: list T1)(l12 l22: list T2),
  length l11 = length l12 /\ length l21 = length l22 -> length(l11 ++ l21) = length(l12 ++ l22).
Proof. intros. destruct H. repeat rewrite add_len. rewrite H. rewrite H0. reflexivity. Qed.
 