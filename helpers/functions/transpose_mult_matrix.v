From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Nat.

(*file useful when executing output file of converter*)

From Coquelicot Require Import Coquelicot.

From CoqE2EAI Require Import neural_networks piecewise_affine.
From CoqE2EAI Require Import string_to_number.

Definition transpose {n m}(matrix: matrix n m) := mk_matrix m n (fun i j => coeff_mat (real_of_string "0"%string) matrix j i).
