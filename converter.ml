
type __ = Obj.t

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n0 m =
  match n0 with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

(** val eqb : nat -> nat -> bool **)

let rec eqb n0 m =
  match n0 with
  | O -> (match m with
          | O -> true
          | S _ -> false)
  | S n' -> (match m with
             | O -> false
             | S m' -> eqb n' m')

(** val leb : nat -> nat -> bool **)

let rec leb n0 m =
  match n0 with
  | O -> true
  | S n' -> (match m with
             | O -> false
             | S m' -> leb n' m')

(** val last : 'a1 list -> 'a1 -> 'a1 **)

let rec last l d =
  match l with
  | [] -> d
  | a :: l0 -> (match l0 with
                | [] -> a
                | _ :: _ -> last l0 d)

(** val removelast : 'a1 list -> 'a1 list **)

let rec removelast = function
| [] -> []
| a :: l0 -> (match l0 with
              | [] -> []
              | _ :: _ -> a :: (removelast l0))

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t3 -> (f a) :: (map f t3)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| [] -> None
| x :: tl -> if f x then Some x else find f tl

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module N =
 struct
  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.to_nat p
 end

module Coq_N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.add p q))

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Coq_Pos.mul p q))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Coq_Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val pow : n -> n -> n **)

  let pow n0 = function
  | N0 -> Npos XH
  | Npos p0 -> (match n0 with
                | N0 -> N0
                | Npos q -> Npos (Coq_Pos.pow q p0))

  (** val pos_div_eucl : positive -> n -> n * n **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | XH ->
      (match b with
       | N0 -> (N0, (Npos XH))
       | Npos p -> (match p with
                    | XH -> ((Npos XH), N0)
                    | _ -> (N0, (Npos XH))))

  (** val div_eucl : n -> n -> n * n **)

  let div_eucl a b =
    match a with
    | N0 -> (N0, N0)
    | Npos na -> (match b with
                  | N0 -> (N0, a)
                  | Npos _ -> pos_div_eucl na b)

  (** val div : n -> n -> n **)

  let div a b =
    fst (div_eucl a b)

  (** val modulo : n -> n -> n **)

  let modulo a b =
    snd (div_eucl a b)

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.to_nat p

  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Coq_Pos.of_succ_nat n')
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)
 end

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    match n0 with
    | O -> zero
    | S n' ->
      (match p with
       | XI p' -> shift true (loop n' p')
       | XO p' -> shift false (loop n' p')
       | XH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> char **)

let ascii_of_nat a =
  ascii_of_N (Coq_N.of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b :: l' ->
  Coq_N.add (if b then Npos XH else N0)
    (Coq_N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> nat **)

let nat_of_ascii a =
  Coq_N.to_nat (n_of_ascii a)

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val length0 : char list -> nat **)

let rec length0 = function
| [] -> O
| _::s' -> S (length0 s')

(** val substring : nat -> nat -> char list -> char list **)

let rec substring n0 m s0 =
  match n0 with
  | O ->
    (match m with
     | O -> []
     | S m' -> (match s0 with
                | [] -> s0
                | c::s' -> c::(substring O m' s')))
  | S n' -> (match s0 with
             | [] -> s0
             | _::s' -> substring n' m s')

(** val concat : char list -> char list list -> char list **)

let rec concat sep = function
| [] -> []
| x :: xs ->
  (match xs with
   | [] -> x
   | _ :: _ -> append x (append sep (concat sep xs)))

(** val prefix : char list -> char list -> bool **)

let rec prefix s1 s2 =
  match s1 with
  | [] -> true
  | a::s1' ->
    (match s2 with
     | [] -> false
     | b::s2' -> if (=) a b then prefix s1' s2' else false)

(** val index : nat -> char list -> char list -> nat option **)

let rec index n0 s1 s2 = match s2 with
| [] ->
  (match n0 with
   | O -> (match s1 with
           | [] -> Some O
           | _::_ -> None)
   | S _ -> None)
| _::s2' ->
  (match n0 with
   | O ->
     if prefix s1 s2
     then Some O
     else (match index O s1 s2' with
           | Some n1 -> Some (S n1)
           | None -> None)
   | S n' ->
     (match index n' s1 s2' with
      | Some n1 -> Some (S n1)
      | None -> None))

(** val string_of_list_ascii : char list -> char list **)

let rec string_of_list_ascii = function
| [] -> []
| ch :: s1 -> ch::(string_of_list_ascii s1)

(** val list_ascii_of_string : char list -> char list **)

let rec list_ascii_of_string = function
| [] -> []
| ch::s1 -> ch :: (list_ascii_of_string s1)

type t = char list

module Option =
 struct
  (** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

  let bind x f =
    match x with
    | Some x0 -> f x0
    | None -> None
 end

module LString =
 struct
  (** val to_string : t -> char list **)

  let rec to_string = function
  | [] -> []
  | c :: s1 -> c::(to_string s1)

  (** val of_string : char list -> t **)

  let rec of_string = function
  | [] -> []
  | c::s1 -> c :: (of_string s1)

  (** val s : char list -> t **)

  let s =
    of_string

  type t = char list

  module Char =
   struct
    (** val n : char **)

    let n =
      '\n'
   end
 end

type t0 =
| New

type command = __

type answer = __

type 'x t1 =
| Ret of 'x
| Call of command
| Let of __ t1 * (__ -> 'x t1)
| Choose of 'x t1 * 'x t1
| Join of __ t1 * __ t1

module Notations =
 struct
  (** val ret : t0 -> 'a1 -> 'a1 t1 **)

  let ret _ x =
    Ret x

  (** val call : t0 -> command -> answer t1 **)

  let call _ command0 =
    Call command0
 end

type t2 =
| ListFiles of LString.t
| ReadFile of LString.t
| WriteFile of LString.t * LString.t
| DeleteFile of LString.t
| System of LString.t
| Eval of LString.t list
| Print of LString.t
| ReadLine

(** val effect : t0 **)

let effect =
  New

(** val read_file : LString.t -> LString.t option t1 **)

let read_file file_name =
  Obj.magic Notations.call effect (ReadFile file_name)

(** val write_file : LString.t -> LString.t -> bool t1 **)

let write_file file_name content =
  Obj.magic Notations.call effect (WriteFile (file_name, content))

(** val printl : LString.t -> bool t1 **)

let printl message =
  Obj.magic Notations.call effect (Print (app message (LString.Char.n :: [])))

(** val log : LString.t -> unit t1 **)

let log message =
  Let ((Obj.magic printl message), (fun _ -> Notations.ret effect ()))

(** val apply : ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let apply f =
  f

module BigInt =
 struct
  type t = Big_int.big_int

  (** val to_Z_aux :
      t -> 'a1 -> ('a2 -> 'a1) -> ('a2 -> 'a1) -> 'a2 -> ('a2 -> 'a2) -> ('a2
      -> 'a2) -> 'a1 **)

  let to_Z_aux = IoSystem.Big.to_Z_aux

  (** val to_Z : t -> z **)

  let to_Z big =
    to_Z_aux big Z0 (fun x -> Zpos x) (fun x -> Zneg x) XH (fun x -> XO x)
      (fun x -> XI x)
 end

module String =
 struct
  type t = string

  (** val of_lstring : LString.t -> t **)

  let of_lstring = IoSystem.String.of_lstring

  (** val to_lstring : t -> LString.t **)

  let to_lstring = IoSystem.String.to_lstring
 end

module Sys =
 struct
  (** val argv : String.t list **)

  let argv = IoSystem.argv
 end

module Lwt =
 struct
  type 'a t = 'a Lwt.t

  (** val ret : 'a1 -> 'a1 t **)

  let ret = Lwt.return

  (** val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t **)

  let bind = Lwt.bind

  (** val join : 'a1 t -> 'a2 t -> ('a1 * 'a2) t **)

  let join = IoSystem.join

  (** val choose : 'a1 t -> 'a1 t -> 'a1 t **)

  let choose = IoSystem.choose

  (** val launch : 'a1 t -> 'a1 **)

  let launch = Lwt_main.run

  (** val list_files : String.t -> String.t list option t **)

  let list_files = IoSystem.list_files

  (** val read_file : String.t -> String.t option t **)

  let read_file = IoSystem.read_file

  (** val write_file : String.t -> String.t -> bool t **)

  let write_file = IoSystem.write_file

  (** val delete_file : String.t -> bool t **)

  let delete_file = IoSystem.delete_file

  (** val system : String.t -> bool option t **)

  let system = IoSystem.system

  (** val eval :
      String.t list -> ((BigInt.t * String.t) * String.t) option t **)

  let eval = IoSystem.eval

  (** val print : String.t -> bool t **)

  let print = IoSystem.print

  (** val read_line : unit -> String.t option t **)

  let read_line = IoSystem.read_line
 end

(** val eval_command : command -> answer Lwt.t **)

let eval_command c =
  match Obj.magic c with
  | ListFiles folder ->
    Lwt.bind (apply Lwt.list_files (String.of_lstring folder)) (fun files ->
      apply (Obj.magic Lwt.ret)
        (Option.bind files (fun files0 -> Some
          (map String.to_lstring files0))))
  | ReadFile file_name ->
    Lwt.bind (apply Lwt.read_file (String.of_lstring file_name))
      (fun content ->
      apply (Obj.magic Lwt.ret) (option_map String.to_lstring content))
  | WriteFile (file_name, content) ->
    let file_name0 = String.of_lstring file_name in
    let content0 = String.of_lstring content in
    Obj.magic Lwt.write_file file_name0 content0
  | DeleteFile file_name ->
    apply (Obj.magic Lwt.delete_file) (String.of_lstring file_name)
  | System command0 -> Obj.magic Lwt.system (String.of_lstring command0)
  | Eval command0 ->
    let command1 = map String.of_lstring command0 in
    Lwt.bind (Lwt.eval command1) (fun result ->
      Lwt.ret
        (apply
          (Obj.magic option_map (fun result0 ->
            let (y, err) = result0 in
            let (status, output) = y in
            (((BigInt.to_Z status), (String.to_lstring output)),
            (String.to_lstring err)))) result))
  | Print message ->
    let message0 = String.of_lstring message in Obj.magic Lwt.print message0
  | ReadLine ->
    Lwt.bind (Lwt.read_line ()) (fun line ->
      apply (Obj.magic Lwt.ret) (option_map String.to_lstring line))

(** val eval0 : 'a1 t1 -> 'a1 Lwt.t **)

let rec eval0 = function
| Ret x0 -> Lwt.ret x0
| Call command0 -> Obj.magic eval_command command0
| Let (t3, t4) -> Lwt.bind (Obj.magic eval0 t3) (fun x0 -> eval0 (t4 x0))
| Choose (t3, t4) -> Lwt.choose (eval0 t3) (eval0 t4)
| Join (t3, t4) ->
  Obj.magic Lwt.join (eval0 (Obj.magic t3)) (eval0 (Obj.magic t4))

(** val launch0 : (LString.t list -> unit t1) -> unit **)

let launch0 main0 =
  let argv0 = map String.to_lstring Sys.argv in
  Lwt.launch (eval0 (main0 argv0))

type 't error_option =
| Success of 't
| Error of char list

(** val error_option_compose :
    ('a1 -> 'a2 error_option) -> ('a2 -> 'a3 error_option) -> 'a1 -> 'a3
    error_option **)

let error_option_compose f g x =
  match f x with
  | Success fx -> g fx
  | Error s0 -> Error s0

(** val ascii_to_digit : char -> n option **)

let ascii_to_digit ch =
  if (=) ch '0'
  then Some N0
  else if (=) ch '1'
       then Some (Npos XH)
       else if (=) ch '2'
            then Some (Npos (XO XH))
            else if (=) ch '3'
                 then Some (Npos (XI XH))
                 else if (=) ch '4'
                      then Some (Npos (XO (XO XH)))
                      else if (=) ch '5'
                           then Some (Npos (XI (XO XH)))
                           else if (=) ch '6'
                                then Some (Npos (XO (XI XH)))
                                else if (=) ch '7'
                                     then Some (Npos (XI (XI XH)))
                                     else if (=) ch '8'
                                          then Some (Npos (XO (XO (XO XH))))
                                          else if (=) ch '9'
                                               then Some (Npos (XI (XO (XO
                                                      XH))))
                                               else if (=) ch 'a'
                                                    then Some (Npos (XO (XI
                                                           (XO XH))))
                                                    else if (=) ch 'A'
                                                         then Some (Npos (XO
                                                                (XI (XO XH))))
                                                         else if (=) ch 'b'
                                                              then Some (Npos
                                                                    (XI (XI
                                                                    (XO XH))))
                                                              else if 
                                                                    (=) ch 'B'
                                                                   then 
                                                                    Some
                                                                    (Npos (XI
                                                                    (XI (XO
                                                                    XH))))
                                                                   else 
                                                                    if 
                                                                    (=) ch 'c'
                                                                    then 
                                                                    Some
                                                                    (Npos (XO
                                                                    (XO (XI
                                                                    XH))))
                                                                    else 
                                                                    if 
                                                                    (=) ch 'C'
                                                                    then 
                                                                    Some
                                                                    (Npos (XO
                                                                    (XO (XI
                                                                    XH))))
                                                                    else 
                                                                    if 
                                                                    (=) ch 'd'
                                                                    then 
                                                                    Some
                                                                    (Npos (XI
                                                                    (XO (XI
                                                                    XH))))
                                                                    else 
                                                                    if 
                                                                    (=) ch 'D'
                                                                    then 
                                                                    Some
                                                                    (Npos (XI
                                                                    (XO (XI
                                                                    XH))))
                                                                    else 
                                                                    if 
                                                                    (=) ch 'e'
                                                                    then 
                                                                    Some
                                                                    (Npos (XO
                                                                    (XI (XI
                                                                    XH))))
                                                                    else 
                                                                    if 
                                                                    (=) ch 'E'
                                                                    then 
                                                                    Some
                                                                    (Npos (XO
                                                                    (XI (XI
                                                                    XH))))
                                                                    else 
                                                                    if 
                                                                    (=) ch 'f'
                                                                    then 
                                                                    Some
                                                                    (Npos (XI
                                                                    (XI (XI
                                                                    XH))))
                                                                    else 
                                                                    if 
                                                                    (=) ch 'F'
                                                                    then 
                                                                    Some
                                                                    (Npos (XI
                                                                    (XI (XI
                                                                    XH))))
                                                                    else None

type escapeSequence =
| Backslash
| SingleQuote
| DoubleQuote
| BEL
| BS
| FF
| LF
| CR
| TAB
| VT
| Octal of char * char * char
| Hex of char * char

type character =
| Regular of char
| Escape of escapeSequence

(** val isBackslash : char -> bool **)

let isBackslash c =
  let n0 = nat_of_ascii c in
  eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val detect_escape_sequence : char list -> character error_option list **)

let rec detect_escape_sequence = function
| [] -> []
| h :: t3 ->
  if isBackslash h
  then (match t3 with
        | [] ->
          (Error
            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('('::('s'::('t'::('a'::('r'::('t'::('i'::('n'::('g'::(' '::('a'::('n'::(' '::('e'::('s'::('c'::('a'::('p'::('e'::(' '::('s'::('e'::('q'::('u'::('e'::('n'::('c'::('e'::(')'::(' '::('w'::('a'::('s'::(' '::('t'::('h'::('e'::(' '::('l'::('a'::('s'::('t'::(' '::('s'::('y'::('m'::('b'::('o'::('l'::(' '::('o'::('f'::(' '::('t'::('h'::('e'::(' '::('l'::('i'::('n'::('e'::(','::(' '::('h'::('o'::('l'::('d'::('i'::('n'::('g'::(' '::('n'::('o'::(' '::('i'::('n'::('f'::('o'::('r'::('m'::('a'::('t'::('i'::('o'::('n'::('.'::(' '::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
        | h' :: t' ->
          (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
            (fun b b0 b1 b2 b3 b4 b5 b6 ->
            if b
            then if b0
                 then if b1
                      then if b2
                           then (match t' with
                                 | [] ->
                                   (Error
                                     ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                 | first :: l ->
                                   (match l with
                                    | [] ->
                                      (Error
                                        ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                    | second :: rest ->
                                      (Success (Escape (Octal (h', first,
                                        second)))) :: (detect_escape_sequence
                                                        rest)))
                           else if b3
                                then (match t' with
                                      | [] ->
                                        (Error
                                          ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                      | first :: l ->
                                        (match l with
                                         | [] ->
                                           (Error
                                             ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                         | second :: rest ->
                                           (Success (Escape (Octal (h',
                                             first,
                                             second)))) :: (detect_escape_sequence
                                                             rest)))
                                else if b4
                                     then if b5
                                          then (match t' with
                                                | [] ->
                                                  (Error
                                                    ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                | first :: l ->
                                                  (match l with
                                                   | [] ->
                                                     (Error
                                                       ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                   | second :: rest ->
                                                     (Success (Escape (Octal
                                                       (h', first,
                                                       second)))) :: 
                                                       (detect_escape_sequence
                                                         rest)))
                                          else if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      SingleQuote)) :: 
                                                      (detect_escape_sequence
                                                        t')
                                     else (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
                      else (match t' with
                            | [] ->
                              (Error
                                ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                            | first :: l ->
                              (match l with
                               | [] ->
                                 (Error
                                   ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                               | second :: rest ->
                                 (Success (Escape (Octal (h', first,
                                   second)))) :: (detect_escape_sequence rest)))
                 else if b1
                      then (match t' with
                            | [] ->
                              (Error
                                ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                            | first :: l ->
                              (match l with
                               | [] ->
                                 (Error
                                   ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                               | second :: rest ->
                                 (Success (Escape (Octal (h', first,
                                   second)))) :: (detect_escape_sequence rest)))
                      else if b2
                           then (match t' with
                                 | [] ->
                                   (Error
                                     ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                 | first :: l ->
                                   (match l with
                                    | [] ->
                                      (Error
                                        ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                    | second :: rest ->
                                      (Success (Escape (Octal (h', first,
                                        second)))) :: (detect_escape_sequence
                                                        rest)))
                           else if b3
                                then (match t' with
                                      | [] ->
                                        (Error
                                          ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                      | first :: l ->
                                        (match l with
                                         | [] ->
                                           (Error
                                             ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                         | second :: rest ->
                                           (Success (Escape (Octal (h',
                                             first,
                                             second)))) :: (detect_escape_sequence
                                                             rest)))
                                else if b4
                                     then if b5
                                          then if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      BEL)) :: (detect_escape_sequence
                                                                 t')
                                          else (match t' with
                                                | [] ->
                                                  (Error
                                                    ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                | first :: l ->
                                                  (match l with
                                                   | [] ->
                                                     (Error
                                                       ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                   | second :: rest ->
                                                     (Success (Escape (Octal
                                                       (h', first,
                                                       second)))) :: 
                                                       (detect_escape_sequence
                                                         rest)))
                                     else (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
            else if b0
                 then if b1
                      then if b2
                           then if b3
                                then (match t' with
                                      | [] ->
                                        (Error
                                          ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                      | first :: l ->
                                        (match l with
                                         | [] ->
                                           (Error
                                             ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                         | second :: rest ->
                                           (Success (Escape (Octal (h',
                                             first,
                                             second)))) :: (detect_escape_sequence
                                                             rest)))
                                else if b4
                                     then if b5
                                          then if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      LF)) :: (detect_escape_sequence
                                                                t')
                                          else (match t' with
                                                | [] ->
                                                  (Error
                                                    ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                | first :: l ->
                                                  (match l with
                                                   | [] ->
                                                     (Error
                                                       ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                   | second :: rest ->
                                                     (Success (Escape (Octal
                                                       (h', first,
                                                       second)))) :: 
                                                       (detect_escape_sequence
                                                         rest)))
                                     else (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
                           else if b3
                                then if b4
                                     then if b5
                                          then if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      VT)) :: (detect_escape_sequence
                                                                t')
                                          else (match t' with
                                                | [] ->
                                                  (Error
                                                    ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                | first :: l ->
                                                  (match l with
                                                   | [] ->
                                                     (Error
                                                       ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                   | second :: rest ->
                                                     (Success (Escape (Octal
                                                       (h', first,
                                                       second)))) :: 
                                                       (detect_escape_sequence
                                                         rest)))
                                     else (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
                                else if b4
                                     then if b5
                                          then if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      FF)) :: (detect_escape_sequence
                                                                t')
                                          else (match t' with
                                                | [] ->
                                                  (Error
                                                    ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                | first :: l ->
                                                  (match l with
                                                   | [] ->
                                                     (Error
                                                       ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                   | second :: rest ->
                                                     (Success (Escape (Octal
                                                       (h', first,
                                                       second)))) :: 
                                                       (detect_escape_sequence
                                                         rest)))
                                     else (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
                      else if b2
                           then (match t' with
                                 | [] ->
                                   (Error
                                     ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                 | first :: l ->
                                   (match l with
                                    | [] ->
                                      (Error
                                        ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                    | second :: rest ->
                                      (Success (Escape (Octal (h', first,
                                        second)))) :: (detect_escape_sequence
                                                        rest)))
                           else if b3
                                then if b4
                                     then if b5
                                          then if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      CR)) :: (detect_escape_sequence
                                                                t')
                                          else (match t' with
                                                | [] ->
                                                  (Error
                                                    ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                | first :: l ->
                                                  (match l with
                                                   | [] ->
                                                     (Error
                                                       ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                   | second :: rest ->
                                                     (Success (Escape (Octal
                                                       (h', first,
                                                       second)))) :: 
                                                       (detect_escape_sequence
                                                         rest)))
                                     else (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
                                else if b4
                                     then if b5
                                          then if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      BS)) :: (detect_escape_sequence
                                                                t')
                                          else if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      DoubleQuote)) :: 
                                                      (detect_escape_sequence
                                                        t')
                                     else (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
                 else if b1
                      then if b2
                           then if b3
                                then if b4
                                     then (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
                                     else if b5
                                          then if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      Backslash)) :: 
                                                      (detect_escape_sequence
                                                        t')
                                          else (match t' with
                                                | [] ->
                                                  (Error
                                                    ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                | first :: l ->
                                                  (match l with
                                                   | [] ->
                                                     (Error
                                                       ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                   | second :: rest ->
                                                     (Success (Escape (Octal
                                                       (h', first,
                                                       second)))) :: 
                                                       (detect_escape_sequence
                                                         rest)))
                                else (match t' with
                                      | [] ->
                                        (Error
                                          ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                      | first :: l ->
                                        (match l with
                                         | [] ->
                                           (Error
                                             ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                         | second :: rest ->
                                           (Success (Escape (Octal (h',
                                             first,
                                             second)))) :: (detect_escape_sequence
                                                             rest)))
                           else if b3
                                then if b4
                                     then if b5
                                          then if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (Success (Escape
                                                      TAB)) :: (detect_escape_sequence
                                                                 t')
                                          else (match t' with
                                                | [] ->
                                                  (Error
                                                    ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                | first :: l ->
                                                  (match l with
                                                   | [] ->
                                                     (Error
                                                       ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                   | second :: rest ->
                                                     (Success (Escape (Octal
                                                       (h', first,
                                                       second)))) :: 
                                                       (detect_escape_sequence
                                                         rest)))
                                     else (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
                                else (match t' with
                                      | [] ->
                                        (Error
                                          ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                      | first :: l ->
                                        (match l with
                                         | [] ->
                                           (Error
                                             ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                         | second :: rest ->
                                           (Success (Escape (Octal (h',
                                             first,
                                             second)))) :: (detect_escape_sequence
                                                             rest)))
                      else if b2
                           then if b3
                                then if b4
                                     then if b5
                                          then if b6
                                               then (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Octal (h',
                                                            first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                               else (match t' with
                                                     | [] ->
                                                       (Error
                                                         ('A'::(' '::('\\'::('x'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('w'::('o'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('h'::('e'::('x'::('a'::('d'::('e'::('c'::('i'::('m'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                     | first :: l ->
                                                       (match l with
                                                        | [] ->
                                                          (Error
                                                            ('A'::(' '::('\\'::('x'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('w'::('o'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('h'::('e'::('x'::('a'::('d'::('e'::('c'::('i'::('m'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                        | second :: rest ->
                                                          (Success (Escape
                                                            (Hex (first,
                                                            second)))) :: 
                                                            (detect_escape_sequence
                                                              rest)))
                                          else (match t' with
                                                | [] ->
                                                  (Error
                                                    ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                | first :: l ->
                                                  (match l with
                                                   | [] ->
                                                     (Error
                                                       ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                                   | second :: rest ->
                                                     (Success (Escape (Octal
                                                       (h', first,
                                                       second)))) :: 
                                                       (detect_escape_sequence
                                                         rest)))
                                     else (match t' with
                                           | [] ->
                                             (Error
                                               ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                           | first :: l ->
                                             (match l with
                                              | [] ->
                                                (Error
                                                  ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                              | second :: rest ->
                                                (Success (Escape (Octal (h',
                                                  first,
                                                  second)))) :: (detect_escape_sequence
                                                                  rest)))
                                else (match t' with
                                      | [] ->
                                        (Error
                                          ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                      | first :: l ->
                                        (match l with
                                         | [] ->
                                           (Error
                                             ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                         | second :: rest ->
                                           (Success (Escape (Octal (h',
                                             first,
                                             second)))) :: (detect_escape_sequence
                                                             rest)))
                           else (match t' with
                                 | [] ->
                                   (Error
                                     ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                 | first :: l ->
                                   (match l with
                                    | [] ->
                                      (Error
                                        ('A'::(' '::('b'::('a'::('c'::('k'::('s'::('l'::('a'::('s'::('h'::(' '::('t'::('h'::('a'::('t'::(' '::('i'::('n'::('d'::('i'::('c'::('a'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(' '::('n'::('e'::('e'::('d'::('s'::(' '::('a'::('t'::(' '::('l'::('e'::('a'::('s'::('t'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('c'::('h'::('a'::('r'::('a'::('c'::('t'::('e'::('r'::('s'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::('i'::('n'::('g'::(' '::('t'::('h'::('e'::(' '::('o'::('c'::('t'::('a'::('l'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []
                                    | second :: rest ->
                                      (Success (Escape (Octal (h', first,
                                        second)))) :: (detect_escape_sequence
                                                        rest))))
            h')
  else (Success (Regular h)) :: (detect_escape_sequence t3)

(** val list_error_option_to_error_option_list :
    'a1 error_option list -> 'a1 list error_option **)

let rec list_error_option_to_error_option_list = function
| [] -> Success []
| h :: t3 ->
  (match h with
   | Success e ->
     (match list_error_option_to_error_option_list t3 with
      | Success t' -> Success (e :: t')
      | Error e0 -> Error e0)
   | Error e -> Error e)

(** val nat_of_ascii0 : char -> nat error_option **)

let nat_of_ascii0 c =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then if b0
         then if b1
              then if b2
                   then Error
                          ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   else if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success (S (S (S (S (S (S (S
                                              O)))))))
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              else if b2
                   then Error
                          ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   else if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success (S (S (S O)))
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         else if b1
              then if b2
                   then Error
                          ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   else if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success (S (S (S (S (S O)))))
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              else if b2
                   then if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success (S (S (S (S (S (S (S (S
                                              (S O)))))))))
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   else if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success (S O)
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    else if b0
         then if b1
              then if b2
                   then Error
                          ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   else if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success (S (S (S (S (S (S O))))))
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              else if b2
                   then Error
                          ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   else if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success (S (S O))
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         else if b1
              then if b2
                   then Error
                          ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   else if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success (S (S (S (S O))))
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              else if b2
                   then if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success (S (S (S (S (S (S (S (S
                                              O))))))))
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   else if b3
                        then if b4
                             then if b5
                                  then Error
                                         ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b6
                                       then Error
                                              ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else Success O
                             else Error
                                    ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('n'::('a'::('t'::('_'::('o'::('f'::('_'::('a'::('s'::('s'::('c'::('i'::('i'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('d'::('i'::('g'::('i'::('t'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    c

(** val ascii_of_octal : char -> char -> char -> char error_option **)

let ascii_of_octal o1 o2 o3 =
  match nat_of_ascii0 o1 with
  | Success n1 ->
    if (&&) (leb O n1) (leb n1 (S (S (S O))))
    then (match nat_of_ascii0 o2 with
          | Success n2 ->
            if (&&) (leb O n2) (leb n2 (S (S (S (S (S (S (S O))))))))
            then (match nat_of_ascii0 o3 with
                  | Success n3 ->
                    if (&&) (leb O n3) (leb n3 (S (S (S (S (S (S (S O))))))))
                    then Success
                           (ascii_of_nat
                             (add
                               (add
                                 (mul (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                   (S (S (S (S (S (S (S (S (S
                                   O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                   n1)
                                 (mul (S (S (S (S (S (S (S (S O)))))))) n2))
                               n3))
                    else Error
                           ('O'::('c'::('t'::('a'::('l'::(':'::(' '::('t'::('h'::('i'::('r'::('d'::(' '::('d'::('i'::('g'::('i'::('t'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('b'::('e'::('t'::('w'::('e'::('e'::('n'::(' '::('0'::(' '::('a'::('n'::('d'::(' '::('7'::('.'::[])))))))))))))))))))))))))))))))))))))))))))
                  | Error e -> Error e)
            else Error
                   ('O'::('c'::('t'::('a'::('l'::(':'::(' '::('s'::('e'::('c'::('o'::('n'::('d'::(' '::('d'::('i'::('g'::('i'::('t'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('b'::('e'::('t'::('w'::('e'::('e'::('n'::(' '::('0'::(' '::('a'::('n'::('d'::(' '::('7'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))
          | Error e -> Error e)
    else Error
           ('O'::('c'::('t'::('a'::('l'::(':'::(' '::('f'::('i'::('r'::('s'::('t'::(' '::('d'::('i'::('g'::('i'::('t'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('b'::('e'::('t'::('w'::('e'::('e'::('n'::(' '::('0'::(' '::('a'::('n'::('d'::(' '::('3'::('.'::[])))))))))))))))))))))))))))))))))))))))))))
  | Error e -> Error e

(** val ascii_of_hex : char -> char -> char error_option **)

let ascii_of_hex h1 h2 =
  match ascii_to_digit h1 with
  | Some n1 ->
    (match ascii_to_digit h2 with
     | Some n2 ->
       Success
         (ascii_of_nat
           (add
             (mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               O)))))))))))))))) (N.to_nat n1)) (N.to_nat n2)))
     | None ->
       Error
         ('a'::('s'::('c'::('i'::('i'::('_'::('o'::('f'::('_'::('h'::('e'::('x'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('h'::('e'::('x'::('-'::('d'::('i'::('g'::('i'::('t'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | None ->
    Error
      ('a'::('s'::('c'::('i'::('i'::('_'::('o'::('f'::('_'::('h'::('e'::('x'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::('n'::(' '::('a'::('s'::('c'::('i'::('i'::(' '::('t'::('h'::('a'::('t'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('r'::('e'::('p'::('r'::('e'::('s'::('e'::('n'::('t'::(' '::('a'::(' '::('h'::('e'::('x'::('-'::('d'::('i'::('g'::('i'::('t'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii_of_character : character -> char error_option **)

let ascii_of_character = function
| Regular a -> Success a
| Escape seq ->
  (match seq with
   | Backslash -> Success '\\'
   | SingleQuote -> Success '\''
   | DoubleQuote -> Success '"'
   | BEL -> Success (ascii_of_nat (S (S (S (S (S (S (S O))))))))
   | BS -> Success (ascii_of_nat (S (S (S (S (S (S (S (S O)))))))))
   | FF ->
     Success (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))
   | LF -> Success (ascii_of_nat (S (S (S (S (S (S (S (S (S (S O)))))))))))
   | CR ->
     Success
       (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))
   | TAB -> Success (ascii_of_nat (S (S (S (S (S (S (S (S (S O))))))))))
   | VT ->
     Success (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S O))))))))))))
   | Octal (o1, o2, o3) -> ascii_of_octal o1 o2 o3
   | Hex (h1, h2) -> ascii_of_hex h1 h2)

(** val escapeSequenceExtractor : char list -> char list error_option **)

let escapeSequenceExtractor l =
  match list_error_option_to_error_option_list (detect_escape_sequence l) with
  | Success charlist ->
    list_error_option_to_error_option_list (map ascii_of_character charlist)
  | Error e -> Error e

(** val split_string_dot_first : char list -> char list * char list **)

let split_string_dot_first s0 =
  match index O ('.'::[]) s0 with
  | Some i ->
    let l = length0 s0 in
    ((substring O (add i (S O)) s0), (substring (add i (S O)) l s0))
  | None -> ([], s0)

(** val split_string_dot_second : char list -> char list * char list **)

let split_string_dot_second s0 =
  match index O ('.'::[]) s0 with
  | Some i -> let l = length0 s0 in ((substring O i s0), (substring i l s0))
  | None -> ([], s0)

(** val nToDigit : n -> char **)

let nToDigit = function
| N0 -> '0'
| Npos p ->
  (match p with
   | XI p0 ->
     (match p0 with
      | XI p1 -> (match p1 with
                  | XH -> '7'
                  | _ -> '9')
      | XO p1 -> (match p1 with
                  | XH -> '5'
                  | _ -> '9')
      | XH -> '3')
   | XO p0 ->
     (match p0 with
      | XI p1 -> (match p1 with
                  | XH -> '6'
                  | _ -> '9')
      | XO p1 ->
        (match p1 with
         | XI _ -> '9'
         | XO p2 -> (match p2 with
                     | XH -> '8'
                     | _ -> '9')
         | XH -> '4')
      | XH -> '2')
   | XH -> '1')

(** val writeNAux : nat -> n -> char list -> char list **)

let rec writeNAux time n0 acc =
  let acc' = (nToDigit (Coq_N.modulo n0 (Npos (XO (XI (XO XH))))))::acc in
  (match time with
   | O -> acc'
   | S time' ->
     (match Coq_N.div n0 (Npos (XO (XI (XO XH)))) with
      | N0 -> acc'
      | Npos p -> writeNAux time' (Npos p) acc'))

(** val writeN : nat -> n -> char list **)

let writeN depth n0 =
  writeNAux depth n0 []

(** val bit_of_bool : bool -> char **)

let bit_of_bool = function
| true -> '1'
| false -> '0'

(** val bitstring_of_ascii : char -> char list **)

let bitstring_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 b c d e f g h ->
    string_of_list_ascii
      (map bit_of_bool
        (h :: (g :: (f :: (e :: (d :: (c :: (b :: (a0 :: []))))))))))
    a

(** val firstFour : 'a1 list -> 'a1 list **)

let firstFour = function
| [] -> []
| l1 :: l0 ->
  (match l0 with
   | [] -> l1 :: []
   | l2 :: l5 ->
     (match l5 with
      | [] -> l1 :: (l2 :: [])
      | l3 :: l6 ->
        (match l6 with
         | [] -> l1 :: (l2 :: (l3 :: []))
         | l4 :: _ -> l1 :: (l2 :: (l3 :: (l4 :: []))))))

(** val little_endian : char list list -> char list **)

let rec little_endian l =
  let ff = firstFour l in
  (match l with
   | [] -> []
   | _ :: l0 ->
     (match l0 with
      | [] -> concat [] (rev ff)
      | _ :: l1 ->
        (match l1 with
         | [] -> concat [] (rev ff)
         | _ :: l2 ->
           (match l2 with
            | [] -> concat [] (rev ff)
            | _ :: t3 -> append (concat [] (rev ff)) (little_endian t3)))))

(** val binary_to_decimal_rec : bool list -> nat **)

let rec binary_to_decimal_rec = function
| [] -> O
| h :: t3 ->
  if h
  then add (S O) (mul (S (S O)) (binary_to_decimal_rec t3))
  else mul (S (S O)) (binary_to_decimal_rec t3)

(** val binary_to_decimal : bool list -> nat **)

let binary_to_decimal bitstring =
  binary_to_decimal_rec (rev bitstring)

(** val list_bool_of_string : char list -> bool list error_option **)

let rec list_bool_of_string = function
| [] -> Success []
| c::t3 ->
  (match list_bool_of_string t3 with
   | Success l ->
     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
       (fun b b0 b1 b2 b3 b4 b5 b6 ->
       if b
       then if b0
            then Error
                   ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
            else if b1
                 then Error
                        ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 else if b2
                      then Error
                             ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                      else if b3
                           then if b4
                                then if b5
                                     then Error
                                            ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                     else if b6
                                          then Error
                                                 ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          else Success (true :: l)
                                else Error
                                       ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                           else Error
                                  ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
       else if b0
            then Error
                   ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
            else if b1
                 then Error
                        ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 else if b2
                      then Error
                             ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                      else if b3
                           then if b4
                                then if b5
                                     then Error
                                            ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                     else if b6
                                          then Error
                                                 ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          else Success (false :: l)
                                else Error
                                       ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))
                           else Error
                                  ('l'::('i'::('s'::('t'::('_'::('b'::('o'::('o'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(':'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('0'::(' '::('o'::('r'::(' '::('1'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       c
   | Error e -> Error e)

(** val count_dot : char list -> nat **)

let rec count_dot = function
| [] -> O
| c::s' ->
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then count_dot s'
    else if b0
         then if b1
              then if b2
                   then if b3
                        then count_dot s'
                        else if b4
                             then if b5
                                  then count_dot s'
                                  else if b6
                                       then count_dot s'
                                       else add (S O) (count_dot s')
                             else count_dot s'
                   else count_dot s'
              else count_dot s'
         else count_dot s')
    c

(** val binary_to_decimal_after_dot_precise : bool list -> n -> n -> n **)

let rec binary_to_decimal_after_dot_precise l precision counter =
  match l with
  | [] -> N0
  | h :: t3 ->
    if h
    then Coq_N.add (Coq_N.div precision counter)
           (binary_to_decimal_after_dot_precise t3 precision
             (Coq_N.mul counter (Npos (XO XH))))
    else binary_to_decimal_after_dot_precise t3 precision
           (Coq_N.mul counter (Npos (XO XH)))

(** val binary_to_decimal_after_dot : bool list -> n **)

let binary_to_decimal_after_dot l =
  binary_to_decimal_after_dot_precise (true :: l)
    (Coq_N.pow (Npos (XO (XI (XO XH)))) (Coq_N.of_nat (length (true :: l))))
    (Npos XH)

(** val remove_first_char : char list -> char list **)

let remove_first_char = function
| [] -> []
| _::s' -> s'

(** val bin_to_dec : char list -> nat -> char list error_option **)

let bin_to_dec s0 n0 =
  match count_dot s0 with
  | O ->
    (match list_bool_of_string s0 with
     | Success l -> Success (writeN n0 (Coq_N.of_nat (binary_to_decimal l)))
     | Error e -> Error e)
  | S n1 ->
    (match n1 with
     | O ->
       let tuple = split_string_dot_second s0 in
       (match list_bool_of_string (fst tuple) with
        | Success l ->
          let firstnum = binary_to_decimal l in
          (match snd tuple with
           | [] ->
             Error
               ('i'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::('n'::('o'::(' '::('d'::('o'::('t'::(' '::('w'::('a'::('s'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('w'::('h'::('i'::('l'::('e'::(' '::('c'::('o'::('u'::('n'::('t'::('i'::('n'::('g'::(' '::('o'::('n'::('e'::(' '::('('::('b'::('i'::('n'::('_'::('t'::('o'::('_'::('d'::('e'::('c'::('-'::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(')'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           | c::s1 ->
             (match list_bool_of_string s1 with
              | Success l' ->
                Success
                  (append (writeN n0 (Coq_N.of_nat firstnum))
                    (c::(remove_first_char
                          (writeN n0 (binary_to_decimal_after_dot l')))))
              | Error e -> Error e))
        | Error e -> Error e)
     | S _ ->
       Error
         ('b'::('i'::('n'::('_'::('t'::('o'::('_'::('d'::('e'::('c'::(':'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('z'::('e'::('r'::('o'::(' '::('o'::('r'::(' '::('e'::('x'::('a'::('c'::('l'::('t'::('y'::(' '::('o'::('n'::('e'::(' '::('d'::('o'::('t'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val bin_to_dec_z : char list -> nat -> char list error_option **)

let bin_to_dec_z s0 n0 =
  match s0 with
  | [] -> bin_to_dec s0 n0
  | a::rest ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b b0 b1 b2 b3 b4 b5 b6 ->
      if b
      then if b0
           then bin_to_dec s0 n0
           else if b1
                then if b2
                     then if b3
                          then bin_to_dec s0 n0
                          else if b4
                               then if b5
                                    then bin_to_dec s0 n0
                                    else if b6
                                         then bin_to_dec s0 n0
                                         else (match bin_to_dec rest n0 with
                                               | Success dec ->
                                                 Success ('-'::dec)
                                               | Error e -> Error e)
                               else bin_to_dec s0 n0
                     else bin_to_dec s0 n0
                else bin_to_dec s0 n0
      else bin_to_dec s0 n0)
      a

(** val isDot : char -> bool **)

let isDot c =
  let n0 = nat_of_ascii c in
  eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))

(** val shift_dot_right_rec : char list -> char list -> nat -> char list **)

let rec shift_dot_right_rec s0 buf = function
| O -> (match s0 with
        | [] -> buf
        | _::_ -> append buf (append ('.'::[]) s0))
| S n0 ->
  (match s0 with
   | [] -> shift_dot_right_rec [] (append buf ('0'::[])) n0
   | c::t3 -> shift_dot_right_rec t3 (append buf (c::[])) n0)

(** val shift_dot_right : char list -> nat -> char list error_option **)

let shift_dot_right s0 times =
  let d = split_string_dot_second s0 in
  (match snd d with
   | [] ->
     Error
       ('i'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::('n'::('o'::(' '::('d'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('w'::('h'::('e'::('r'::('e'::(' '::('s'::('o'::('m'::('e'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('('::('s'::('h'::('i'::('f'::('t'::('_'::('d'::('o'::('t'::('_'::('r'::('i'::('g'::('h'::('t'::('-'::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(')'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   | dot::t3 ->
     if isDot dot
     then Success (append (fst d) (shift_dot_right_rec t3 [] times))
     else Error
            ('i'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::('n'::('o'::(' '::('d'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('w'::('h'::('e'::('r'::('e'::(' '::('s'::('o'::('m'::('e'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('('::('s'::('h'::('i'::('f'::('t'::('_'::('d'::('o'::('t'::('_'::('r'::('i'::('g'::('h'::('t'::('-'::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(')'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val reverse_string : char list -> char list **)

let reverse_string s0 =
  string_of_list_ascii (rev (list_ascii_of_string s0))

(** val shift_dot_left_rec : char list -> char list -> nat -> char list **)

let rec shift_dot_left_rec s0 buf = function
| O ->
  (match s0 with
   | [] -> append buf ('.'::('0'::[]))
   | _::_ -> append buf (append ('.'::[]) s0))
| S n0 ->
  (match s0 with
   | [] -> shift_dot_left_rec [] (append buf ('0'::[])) n0
   | c::t3 -> shift_dot_left_rec t3 (append buf (c::[])) n0)

(** val shift_dot_left : char list -> nat -> char list error_option **)

let shift_dot_left s0 times =
  let d = split_string_dot_first s0 in
  (match reverse_string (fst d) with
   | [] ->
     Error
       ('i'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::('n'::('o'::(' '::('d'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('w'::('h'::('e'::('r'::('e'::(' '::('s'::('o'::('m'::('e'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('('::('s'::('h'::('i'::('f'::('t'::('_'::('d'::('o'::('t'::('_'::('l'::('e'::('f'::('t'::('-'::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(')'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   | dot::t3 ->
     if isDot dot
     then Success
            (append
              (reverse_string
                (shift_dot_left_rec (reverse_string t3) [] times)) (snd d))
     else Error
            ('i'::('n'::('t'::('e'::('r'::('n'::('a'::('l'::(' '::('e'::('r'::('r'::('o'::('r'::(':'::(' '::('n'::('o'::(' '::('d'::('o'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('w'::('h'::('e'::('r'::('e'::(' '::('s'::('o'::('m'::('e'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('b'::('e'::(' '::('('::('s'::('h'::('i'::('f'::('t'::('_'::('d'::('o'::('t'::('_'::('l'::('e'::('f'::('t'::('-'::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(')'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val nat_of_Z : z -> bool * nat **)

let nat_of_Z = function
| Z0 -> (false, O)
| Zpos p -> (false, (Coq_Pos.to_nat p))
| Zneg p -> (true, (Coq_Pos.to_nat p))

(** val iEEE754 : char list -> char list error_option **)

let iEEE754 bitstring =
  match length0 bitstring with
  | O ->
    Error
      ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
  | S n0 ->
    (match n0 with
     | O ->
       Error
         ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
     | S n1 ->
       (match n1 with
        | O ->
          Error
            ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
        | S n2 ->
          (match n2 with
           | O ->
             Error
               ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
           | S n3 ->
             (match n3 with
              | O ->
                Error
                  ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
              | S n4 ->
                (match n4 with
                 | O ->
                   Error
                     ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                 | S n5 ->
                   (match n5 with
                    | O ->
                      Error
                        ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                    | S n6 ->
                      (match n6 with
                       | O ->
                         Error
                           ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                       | S n7 ->
                         (match n7 with
                          | O ->
                            Error
                              ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                          | S n8 ->
                            (match n8 with
                             | O ->
                               Error
                                 ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                             | S n9 ->
                               (match n9 with
                                | O ->
                                  Error
                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                | S n10 ->
                                  (match n10 with
                                   | O ->
                                     Error
                                       ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                   | S n11 ->
                                     (match n11 with
                                      | O ->
                                        Error
                                          ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      | S n12 ->
                                        (match n12 with
                                         | O ->
                                           Error
                                             ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                         | S n13 ->
                                           (match n13 with
                                            | O ->
                                              Error
                                                ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                            | S n14 ->
                                              (match n14 with
                                               | O ->
                                                 Error
                                                   ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                               | S n15 ->
                                                 (match n15 with
                                                  | O ->
                                                    Error
                                                      ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                  | S n16 ->
                                                    (match n16 with
                                                     | O ->
                                                       Error
                                                         ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                     | S n17 ->
                                                       (match n17 with
                                                        | O ->
                                                          Error
                                                            ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                        | S n18 ->
                                                          (match n18 with
                                                           | O ->
                                                             Error
                                                               ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                           | S n19 ->
                                                             (match n19 with
                                                              | O ->
                                                                Error
                                                                  ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                              | S n20 ->
                                                                (match n20 with
                                                                 | O ->
                                                                   Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                 | S n21 ->
                                                                   (match n21 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n22 ->
                                                                    (match n22 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n23 ->
                                                                    (match n23 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n24 ->
                                                                    (match n24 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n25 ->
                                                                    (match n25 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n26 ->
                                                                    (match n26 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n27 ->
                                                                    (match n27 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n28 ->
                                                                    (match n28 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n29 ->
                                                                    (match n29 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n30 ->
                                                                    (match n30 with
                                                                    | O ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | S n31 ->
                                                                    (match n31 with
                                                                    | O ->
                                                                    (match 
                                                                    list_bool_of_string
                                                                    (substring
                                                                    O (S O)
                                                                    bitstring) with
                                                                    | Success sign ->
                                                                    (match 
                                                                    list_bool_of_string
                                                                    (substring
                                                                    (S O) (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))
                                                                    bitstring) with
                                                                    | Success exponent ->
                                                                    let mantissa =
                                                                    substring
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O)))))))))
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O)))))))))))))))))))))))
                                                                    bitstring
                                                                    in
                                                                    let b =
                                                                    Zpos (XI
                                                                    (XI (XI
                                                                    (XI (XI
                                                                    (XI
                                                                    XH))))))
                                                                    in
                                                                    let e =
                                                                    Z.sub
                                                                    (Z.of_nat
                                                                    (binary_to_decimal
                                                                    exponent))
                                                                    b
                                                                    in
                                                                    let m =
                                                                    concat []
                                                                    (('1'::('.'::[])) :: (mantissa :: []))
                                                                    in
                                                                    let s0 =
                                                                    match sign with
                                                                    | [] -> []
                                                                    | b0 :: l ->
                                                                    if b0
                                                                    then 
                                                                    (match l with
                                                                    | [] ->
                                                                    '-'::[]
                                                                    | _ :: _ ->
                                                                    [])
                                                                    else []
                                                                    in
                                                                    let enat =
                                                                    nat_of_Z e
                                                                    in
                                                                    if 
                                                                    fst enat
                                                                    then 
                                                                    (match 
                                                                    shift_dot_left
                                                                    m
                                                                    (snd enat) with
                                                                    | Success n32 ->
                                                                    Success
                                                                    (append
                                                                    s0 n32)
                                                                    | Error e0 ->
                                                                    Error e0)
                                                                    else 
                                                                    (match 
                                                                    shift_dot_right
                                                                    m
                                                                    (snd enat) with
                                                                    | Success n32 ->
                                                                    Success
                                                                    (append
                                                                    s0 n32)
                                                                    | Error e0 ->
                                                                    Error e0)
                                                                    | Error e ->
                                                                    Error e)
                                                                    | Error e ->
                                                                    Error e)
                                                                    | S _ ->
                                                                    Error
                                                                    ('I'::('E'::('E'::('E'::('7'::('5'::('4'::(':'::(' '::('T'::('h'::('e'::(' '::('b'::('i'::('t'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('m'::('u'::('s'::('t'::(' '::('c'::('o'::('n'::('t'::('a'::('i'::('n'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('3'::('2'::(' '::('b'::('i'::('t'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val unpack : nat -> char list -> char list error_option **)

let unpack precision s0 =
  match iEEE754 (little_endian (map bitstring_of_ascii s0)) with
  | Success binfloat -> bin_to_dec_z binfloat precision
  | Error e -> Error e

(** val fourPacks : 'a1 list -> 'a1 list list **)

let rec fourPacks = function
| [] -> []
| a :: l0 ->
  (match l0 with
   | [] -> (a :: []) :: []
   | b :: l1 ->
     (match l1 with
      | [] -> (a :: (b :: [])) :: []
      | c :: l2 ->
        (match l2 with
         | [] -> (a :: (b :: (c :: []))) :: []
         | d :: t3 -> (a :: (b :: (c :: (d :: [])))) :: (fourPacks t3))))

(** val list_error_option_to_error_option_list0 :
    'a1 error_option list -> 'a1 list error_option **)

let rec list_error_option_to_error_option_list0 = function
| [] -> Success []
| h :: t3 ->
  (match h with
   | Success e ->
     (match list_error_option_to_error_option_list0 t3 with
      | Success t' -> Success (e :: t')
      | Error e0 -> Error e0)
   | Error e -> Error e)

(** val unpack_mult : nat -> char list -> char list list error_option **)

let unpack_mult precision s0 =
  match escapeSequenceExtractor (list_ascii_of_string s0) with
  | Success seq ->
    list_error_option_to_error_option_list0
      (map (unpack precision) (fourPacks seq))
  | Error e -> Error e

(** val stateful_map :
    'a1 list -> 'a3 -> ('a3 -> 'a1 -> 'a2) -> ('a3 -> 'a1 -> 'a3) -> 'a2 list **)

let rec stateful_map l state f getState0 =
  match l with
  | [] -> []
  | h :: t3 ->
    let next_state = getState0 state h in
    (f state h) :: (stateful_map t3 next_state f getState0)

(** val isWhite : char -> bool **)

let isWhite c =
  let n0 = nat_of_ascii c in
  (||)
    ((||)
      (eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))
      (eqb n0 (S (S (S (S (S (S (S (S (S O)))))))))))
    ((||) (eqb n0 (S (S (S (S (S (S (S (S (S (S O)))))))))))
      (eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))

(** val removeWhitesAtBeginning : char list -> char list **)

let rec removeWhitesAtBeginning s0 = match s0 with
| [] -> []
| c::s' -> if isWhite c then removeWhitesAtBeginning s' else s0

(** val is_raw_data : char list -> bool **)

let is_raw_data s0 =
  let raw_data_possible =
    substring O (S (S (S (S (S (S (S (S O)))))))) (removeWhitesAtBeginning s0)
  in
  eqb0 raw_data_possible
    ('r'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))

(** val is_data_type : char list -> bool **)

let is_data_type s0 =
  let data_type_possible =
    substring O (S (S (S (S (S (S (S (S (S O)))))))))
      (removeWhitesAtBeginning s0)
  in
  eqb0 data_type_possible
    ('d'::('a'::('t'::('a'::('_'::('t'::('y'::('p'::('e'::[])))))))))

(** val remove_at_beginning : char list -> nat -> char list **)

let rec remove_at_beginning s0 = function
| O -> s0
| S n' -> (match s0 with
           | [] -> s0
           | _::s' -> remove_at_beginning s' n')

(** val reverse_string0 : char list -> char list **)

let reverse_string0 s0 =
  string_of_list_ascii (rev (list_ascii_of_string s0))

(** val remove_at_end : char list -> nat -> char list **)

let remove_at_end s0 n0 =
  reverse_string0 (remove_at_beginning (reverse_string0 s0) n0)

(** val extract_raw_data : char list -> char list **)

let extract_raw_data s0 =
  remove_at_end
    (remove_at_beginning (removeWhitesAtBeginning s0) (S (S (S (S (S (S (S (S
      (S (S (S O)))))))))))) (S O)

(** val extract_data_type : char list -> char list **)

let extract_data_type s0 =
  remove_at_beginning (removeWhitesAtBeginning s0) (S (S (S (S (S (S (S (S (S
    (S (S O)))))))))))

(** val rearrange_converted_data : char list -> char list **)

let rearrange_converted_data s0 =
  append
    (append
      ('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('d'::(':'::(' '::[]))))))))))))))))
      s0) ('\n'::(' '::(' '::[])))

(** val convert_line : char list -> char list error_option **)

let convert_line s0 =
  if is_raw_data s0
  then (match unpack_mult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S
                O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                (extract_raw_data s0) with
        | Success l -> Success (concat [] (map rearrange_converted_data l))
        | Error e -> Error e)
  else Success s0

(** val convert_line_given_datatype :
    char list -> char list -> char list error_option **)

let convert_line_given_datatype datatype line =
  if is_raw_data line
  then (match datatype with
        | [] ->
          Error
            (append
              ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
              (append datatype
                (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
        | a::s0 ->
          (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
            (fun b b0 b1 b2 b3 b4 b5 b6 ->
            if b
            then if b0
                 then Error
                        (append
                          ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                          (append datatype
                            (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                 else if b1
                      then Error
                             (append
                               ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                               (append datatype
                                 (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                      else if b2
                           then Error
                                  (append
                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                    (append datatype
                                      (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                           else if b3
                                then if b4
                                     then if b5
                                          then Error
                                                 (append
                                                   ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                   (append datatype
                                                     (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                          else if b6
                                               then Error
                                                      (append
                                                        ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                        (append datatype
                                                          (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                               else (match s0 with
                                                     | [] -> convert_line line
                                                     | _::_ ->
                                                       Error
                                                         (append
                                                           ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                           (append datatype
                                                             (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[])))))))))))))))))))))))))))))))
                                     else Error
                                            (append
                                              ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                              (append datatype
                                                (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                else Error
                                       (append
                                         ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                         (append datatype
                                           (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
            else if b0
                 then if b1
                      then if b2
                           then if b3
                                then Error
                                       (append
                                         ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                         (append datatype
                                           (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                else if b4
                                     then Error
                                            (append
                                              ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                              (append datatype
                                                (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                     else if b5
                                          then if b6
                                               then Error
                                                      (append
                                                        ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                        (append datatype
                                                          (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                               else (match s0 with
                                                     | [] ->
                                                       Error
                                                         (append
                                                           ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                           (append datatype
                                                             (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                     | a0::s1 ->
                                                       (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                         (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                         if b7
                                                         then if b8
                                                              then if b9
                                                                   then 
                                                                    if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Error
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('N'::('o'::(' '::('d'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::('h'::('a'::('s'::(' '::('b'::('e'::('e'::('n'::(' '::('g'::('i'::('v'::('e'::('n'::('.'::(' '::('T'::('h'::('e'::(' '::('\''::('d'::('a'::('t'::('a'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('f'::('i'::('e'::('l'::('d'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('b'::('e'::('f'::('o'::('r'::('e'::(' '::('t'::('h'::('e'::(' '::('\''::('r'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('\''::(' '::('f'::('i'::('e'::('l'::('d'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | _::_ ->
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[])))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[])))))))))))))))))))))))))))))))
                                                                    a2)
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[])))))))))))))))))))))))))))))))
                                                                    a1)
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                                   else 
                                                                    Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                              else Error
                                                                    (append
                                                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                    (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                                                         else Error
                                                                (append
                                                                  ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                                  (append
                                                                    datatype
                                                                    (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[])))))))))))))))))))))))))))))))
                                                         a0)
                                          else Error
                                                 (append
                                                   ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                                   (append datatype
                                                     (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                           else Error
                                  (append
                                    ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                                    (append datatype
                                      (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                      else Error
                             (append
                               ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                               (append datatype
                                 (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))
                 else Error
                        (append
                          ('R'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::(':'::(' '::('O'::('N'::('N'::('X'::(' '::('D'::('a'::('t'::('a'::('t'::('y'::('p'::('e'::(' '::[]))))))))))))))))))))))))))))))))))
                          (append datatype
                            (' '::('i'::('s'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[])))))))))))))))))))))))))))))))
            a)
  else Success line

(** val split_lines_rec : char list -> char list -> char list list **)

let rec split_lines_rec s0 buf =
  match s0 with
  | [] -> buf :: []
  | c::s' ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b b0 b1 b2 b3 b4 b5 b6 ->
      if b
      then split_lines_rec s' (append buf (c::[]))
      else if b0
           then if b1
                then split_lines_rec s' (append buf (c::[]))
                else if b2
                     then if b3
                          then split_lines_rec s' (append buf (c::[]))
                          else if b4
                               then split_lines_rec s' (append buf (c::[]))
                               else if b5
                                    then split_lines_rec s'
                                           (append buf (c::[]))
                                    else if b6
                                         then split_lines_rec s'
                                                (append buf (c::[]))
                                         else buf :: (split_lines_rec s' [])
                     else split_lines_rec s' (append buf (c::[]))
           else split_lines_rec s' (append buf (c::[])))
      c

(** val split_lines : char list -> char list list **)

let split_lines s0 =
  split_lines_rec s0 []

(** val getState : char list -> char list -> char list **)

let getState state line =
  if is_data_type line
  then extract_data_type line
  else if is_raw_data line then 'N'::('o'::('n'::('e'::[]))) else state

(** val raw_data_converter : char list -> char list error_option **)

let raw_data_converter s0 =
  let lines = split_lines (string_of_list_ascii s0) in
  let map_convertion =
    list_error_option_to_error_option_list0
      (stateful_map lines ('N'::('o'::('n'::('e'::[]))))
        convert_line_given_datatype getState)
  in
  (match map_convertion with
   | Success s1 ->
     let seperator = '\n'::[] in
     Success (list_ascii_of_string (concat seperator s1))
   | Error e -> Error e)

(** val isWhite0 : char -> bool **)

let isWhite0 c =
  let n0 = nat_of_ascii c in
  (||)
    ((||)
      (eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))
      (eqb n0 (S (S (S (S (S (S (S (S (S O)))))))))))
    ((||) (eqb n0 (S (S (S (S (S (S (S (S (S (S O)))))))))))
      (eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))

(** val isQuotationMark : char -> bool **)

let isQuotationMark c =
  let n0 = nat_of_ascii c in
  eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))

(** val isColon : char -> bool **)

let isColon c =
  let n0 = nat_of_ascii c in
  eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val isLeftBrace : char -> bool **)

let isLeftBrace c =
  let n0 = nat_of_ascii c in
  eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val isRightBrace : char -> bool **)

let isRightBrace c =
  let n0 = nat_of_ascii c in
  eqb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val split_string :
    (char -> bool) -> char list -> char list -> char list list **)

let rec split_string f z0 s0 =
  let revz = match z0 with
             | [] -> []
             | _ :: _ -> (rev z0) :: [] in
  (match s0 with
   | [] -> revz
   | h :: t3 ->
     if f h
     then app (app revz ((h :: []) :: [])) (split_string f [] t3)
     else split_string f (h :: z0) t3)

(** val split_strings : (char -> bool) -> char list list -> char list list **)

let rec split_strings f = function
| [] -> []
| h :: t3 -> app (split_string f [] h) (split_strings f t3)

(** val merge_quotationMark :
    bool -> char list -> char list list -> char list list **)

let rec merge_quotationMark inMarkZone z0 = function
| [] -> z0 :: []
| h :: t3 ->
  if inMarkZone
  then if existsb isQuotationMark h
       then (app z0 h) :: (merge_quotationMark false [] t3)
       else merge_quotationMark true (app z0 h) t3
  else if existsb isQuotationMark h
       then merge_quotationMark true (app z0 h) t3
       else (app z0 h) :: (merge_quotationMark false [] t3)

(** val no_only_white : char list -> bool **)

let no_only_white s0 =
  negb (forallb isWhite0 s0)

(** val tokenizer : char list -> char list list **)

let tokenizer s0 =
  filter no_only_white
    (merge_quotationMark false []
      (split_strings isQuotationMark
        (split_strings isRightBrace
          (split_strings isLeftBrace
            (split_strings isColon (split_string isWhite0 [] s0))))))

(** val eqb_la : char list -> char list -> bool **)

let rec eqb_la s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _ :: _ -> false)
  | h1 :: t3 ->
    (match s2 with
     | [] -> false
     | h2 :: t4 -> if (=) h1 h2 then eqb_la t3 t4 else false)

type tree =
| Leaf of char list
| Subtree of char list * tree list

(** val node_value : tree -> char list **)

let node_value = function
| Leaf v -> v
| Subtree (v, _) -> v

(** val node_children : tree -> tree list **)

let node_children = function
| Leaf _ -> []
| Subtree (_, c) -> c

(** val getFirstChildValue : tree -> char list option **)

let getFirstChildValue t3 =
  let c = node_children t3 in
  (match c with
   | [] -> None
   | h :: _ -> Some (node_value h))

(** val append_at_end : tree -> nat -> char list -> tree **)

let rec append_at_end t3 depth value =
  match depth with
  | O ->
    Subtree ((node_value t3),
      (app (node_children t3) ((Subtree (value, [])) :: [])))
  | S n0 ->
    Subtree ((node_value t3),
      (app (removelast (node_children t3))
        ((append_at_end
           (last (node_children t3) (Leaf
             (list_ascii_of_string
               ('p'::('r'::('o'::('b'::('a'::('b'::('l'::('y'::('_'::('m'::('i'::('s'::('p'::('l'::('a'::('c'::('e'::('d'::('_'::('n'::('o'::('d'::('e'::[]))))))))))))))))))))))))))
           n0 value) :: [])))

(** val inb : char list list -> char list -> bool **)

let rec inb l s0 =
  match l with
  | [] -> false
  | b :: m ->
    if eqb0 (string_of_list_ascii b) (string_of_list_ascii s0)
    then true
    else inb m s0

(** val notInb : char list list -> char list -> bool **)

let rec notInb l s0 =
  match l with
  | [] -> true
  | b :: m ->
    if eqb0 (string_of_list_ascii b) (string_of_list_ascii s0)
    then false
    else notInb m s0

(** val parse_recursive : tree -> char list list -> nat -> bool -> tree **)

let rec parse_recursive built_tree todo_list depth after_colon =
  match todo_list with
  | [] -> built_tree
  | active_token :: todo_list' ->
    if after_colon
    then parse_recursive (append_at_end built_tree depth active_token)
           todo_list' (sub depth (S O)) false
    else (match active_token with
          | [] ->
            parse_recursive (append_at_end built_tree depth active_token)
              todo_list' depth false
          | a :: l ->
            (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
              (fun b b0 b1 b2 b3 b4 b5 b6 ->
              if b
              then if b0
                   then if b1
                        then parse_recursive
                               (append_at_end built_tree depth active_token)
                               todo_list' depth false
                        else if b2
                             then if b3
                                  then if b4
                                       then if b5
                                            then if b6
                                                 then parse_recursive
                                                        (append_at_end
                                                          built_tree depth
                                                          active_token)
                                                        todo_list' depth false
                                                 else (match l with
                                                       | [] ->
                                                         parse_recursive
                                                           built_tree
                                                           todo_list'
                                                           (add depth (S O))
                                                           false
                                                       | _ :: _ ->
                                                         parse_recursive
                                                           (append_at_end
                                                             built_tree depth
                                                             active_token)
                                                           todo_list' depth
                                                           false)
                                            else parse_recursive
                                                   (append_at_end built_tree
                                                     depth active_token)
                                                   todo_list' depth false
                                       else parse_recursive
                                              (append_at_end built_tree depth
                                                active_token) todo_list'
                                              depth false
                                  else parse_recursive
                                         (append_at_end built_tree depth
                                           active_token) todo_list' depth
                                         false
                             else parse_recursive
                                    (append_at_end built_tree depth
                                      active_token) todo_list' depth false
                   else if b1
                        then if b2
                             then if b3
                                  then if b4
                                       then if b5
                                            then if b6
                                                 then parse_recursive
                                                        (append_at_end
                                                          built_tree depth
                                                          active_token)
                                                        todo_list' depth false
                                                 else (match l with
                                                       | [] ->
                                                         parse_recursive
                                                           built_tree
                                                           todo_list'
                                                           (sub depth (S O))
                                                           false
                                                       | _ :: _ ->
                                                         parse_recursive
                                                           (append_at_end
                                                             built_tree depth
                                                             active_token)
                                                           todo_list' depth
                                                           false)
                                            else parse_recursive
                                                   (append_at_end built_tree
                                                     depth active_token)
                                                   todo_list' depth false
                                       else parse_recursive
                                              (append_at_end built_tree depth
                                                active_token) todo_list'
                                              depth false
                                  else parse_recursive
                                         (append_at_end built_tree depth
                                           active_token) todo_list' depth
                                         false
                             else parse_recursive
                                    (append_at_end built_tree depth
                                      active_token) todo_list' depth false
                        else parse_recursive
                               (append_at_end built_tree depth active_token)
                               todo_list' depth false
              else if b0
                   then if b1
                        then parse_recursive
                               (append_at_end built_tree depth active_token)
                               todo_list' depth false
                        else if b2
                             then if b3
                                  then if b4
                                       then if b5
                                            then parse_recursive
                                                   (append_at_end built_tree
                                                     depth active_token)
                                                   todo_list' depth false
                                            else if b6
                                                 then parse_recursive
                                                        (append_at_end
                                                          built_tree depth
                                                          active_token)
                                                        todo_list' depth false
                                                 else (match l with
                                                       | [] ->
                                                         parse_recursive
                                                           built_tree
                                                           todo_list'
                                                           (add depth (S O))
                                                           true
                                                       | _ :: _ ->
                                                         parse_recursive
                                                           (append_at_end
                                                             built_tree depth
                                                             active_token)
                                                           todo_list' depth
                                                           false)
                                       else parse_recursive
                                              (append_at_end built_tree depth
                                                active_token) todo_list'
                                              depth false
                                  else parse_recursive
                                         (append_at_end built_tree depth
                                           active_token) todo_list' depth
                                         false
                             else parse_recursive
                                    (append_at_end built_tree depth
                                      active_token) todo_list' depth false
                   else parse_recursive
                          (append_at_end built_tree depth active_token)
                          todo_list' depth false)
              a)

(** val parser0 : char list list -> tree **)

let parser0 l =
  parse_recursive (Subtree
    ((list_ascii_of_string ('m'::('a'::('i'::('n'::[]))))), [])) l O false

(** val listToString : char list list -> char list **)

let rec listToString = function
| [] -> []
| h :: t3 ->
  (match t3 with
   | [] -> h
   | _ :: _ ->
     app h (app (list_ascii_of_string (','::(' '::[]))) (listToString t3)))

type filterListElement =
| WhiteL of char list * char list list
| BlackL of char list * char list list

(** val whitelist : filterListElement list **)

let whitelist =
  (BlackL ((list_ascii_of_string ('m'::('a'::('i'::('n'::[]))))),
    [])) :: ((BlackL
    ((list_ascii_of_string ('g'::('r'::('a'::('p'::('h'::[])))))),
    [])) :: ((BlackL ((list_ascii_of_string ('n'::('a'::('m'::('e'::[]))))),
    [])) :: ((BlackL ((list_ascii_of_string ('n'::('o'::('d'::('e'::[]))))),
    [])) :: ((BlackL
    ((list_ascii_of_string ('i'::('n'::('p'::('u'::('t'::[])))))),
    [])) :: ((BlackL
    ((list_ascii_of_string ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))),
    [])) :: ((WhiteL
    ((list_ascii_of_string
       ('o'::('p'::('_'::('t'::('y'::('p'::('e'::[])))))))),
    (map list_ascii_of_string
      (('"'::('G'::('e'::('m'::('m'::('"'::[])))))) :: (('"'::('R'::('e'::('l'::('u'::('"'::[])))))) :: []))))) :: ((BlackL
    ((list_ascii_of_string
       ('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::[])))))))))),
    [])) :: ((BlackL ((list_ascii_of_string ('t'::('y'::('p'::('e'::[]))))),
    [])) :: ((BlackL ((list_ascii_of_string ('f'::[])), [])) :: ((BlackL
    ((list_ascii_of_string ('i'::[])), [])) :: ((BlackL
    ((list_ascii_of_string ('s'::[])), [])) :: ((BlackL
    ((list_ascii_of_string ('t'::[])), [])) :: ((BlackL
    ((list_ascii_of_string ('g'::[])), [])) :: ((BlackL
    ((list_ascii_of_string ('f'::('l'::('o'::('a'::('t'::('s'::[]))))))),
    [])) :: ((BlackL ((list_ascii_of_string ('i'::('n'::('t'::('s'::[]))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('s'::('t'::('r'::('i'::('n'::('g'::('s'::[])))))))), [])) :: ((BlackL
    ((list_ascii_of_string
       ('t'::('e'::('n'::('s'::('o'::('r'::('s'::[])))))))), [])) :: ((BlackL
    ((list_ascii_of_string ('g'::('r'::('a'::('p'::('h'::('s'::[]))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))),
    [])) :: ((BlackL ((list_ascii_of_string ('d'::('i'::('m'::('s'::[]))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('d'::('a'::('t'::('a'::('_'::('t'::('y'::('p'::('e'::[])))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('f'::('l'::('o'::('a'::('t'::('_'::('d'::('a'::('t'::('a'::[]))))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('i'::('n'::('t'::('3'::('2'::('_'::('d'::('a'::('t'::('a'::[]))))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('s'::('t'::('r'::('i'::('n'::('g'::('_'::('d'::('a'::('t'::('a'::[])))))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('i'::('n'::('t'::('6'::('4'::('_'::('d'::('a'::('t'::('a'::[]))))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('r'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::[]))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string ('i'::('n'::('p'::('u'::('t'::[])))))),
    [])) :: ((BlackL ((list_ascii_of_string ('t'::('y'::('p'::('e'::[]))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('e'::('l'::('e'::('m'::('_'::('t'::('y'::('p'::('e'::[])))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string ('s'::('h'::('a'::('p'::('e'::[])))))),
    [])) :: ((BlackL ((list_ascii_of_string ('d'::('i'::('m'::[])))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('d'::('i'::('m'::('_'::('v'::('a'::('l'::('u'::('e'::[])))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('d'::('i'::('m'::('_'::('p'::('a'::('r'::('a'::('m'::[])))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('k'::('e'::('y'::('_'::('t'::('y'::('p'::('e'::[]))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('v'::('a'::('l'::('u'::('e'::('_'::('t'::('y'::('p'::('e'::[]))))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('t'::('e'::('n'::('s'::('o'::('r'::('_'::('t'::('y'::('p'::('e'::[])))))))))))),
    [])) :: ((BlackL
    ((list_ascii_of_string
       ('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('d'::[]))))))))))))))),
    [])) :: []))))))))))))))))))))))))))))))))))))))

(** val getAttribute : filterListElement -> char list **)

let getAttribute = function
| WhiteL (a, _) -> a
| BlackL (a, _) -> a

(** val get_value_whitelist_r :
    char list -> filterListElement list -> filterListElement **)

let rec get_value_whitelist_r a = function
| [] -> BlackL (a, [])
| h :: t3 ->
  if eqb_la (getAttribute h) a then h else get_value_whitelist_r a t3

(** val get_value_whitelist : char list -> filterListElement **)

let get_value_whitelist a =
  get_value_whitelist_r a whitelist

(** val attributesAcceptsValue : char list -> char list -> bool **)

let attributesAcceptsValue a v =
  let f = get_value_whitelist a in
  (match f with
   | WhiteL (_, v') -> inb v' v
   | BlackL (_, v') -> notInb v' v)

(** val grab : char list list -> tree -> tree option **)

let rec grab path inputTree =
  match path with
  | [] -> Some inputTree
  | h :: t3 ->
    (match find (fun n0 ->
             eqb0 (string_of_list_ascii h)
               (string_of_list_ascii (node_value n0)))
             (node_children inputTree) with
     | Some found -> grab t3 found
     | None -> None)

(** val grab_value : char list list -> tree -> char list option **)

let grab_value path inputTree =
  match grab path inputTree with
  | Some s0 -> getFirstChildValue s0
  | None -> None

(** val grabAll : char list list -> char list -> tree -> tree list **)

let grabAll path child_name inputTree =
  let tree_opt = grab path inputTree in
  (match tree_opt with
   | Some tree0 ->
     (match tree0 with
      | Leaf _ -> []
      | Subtree (_, c) ->
        filter (fun x ->
          eqb0 (string_of_list_ascii (node_value x)) child_name) c)
   | None -> [])

(** val supportedValues : char list -> char list **)

let supportedValues a =
  let f = get_value_whitelist a in
  (match f with
   | WhiteL (_, l) ->
     app (list_ascii_of_string ('o'::('n'::('l'::('y'::(' '::[]))))))
       (listToString l)
   | BlackL (_, l) ->
     app
       (list_ascii_of_string
         ('e'::('v'::('e'::('r'::('y'::('t'::('h'::('i'::('n'::('g'::(' '::('b'::('u'::('t'::(' '::[]))))))))))))))))
       (listToString l))

(** val createWarningErrorMessage : char list -> tree -> char list **)

let createWarningErrorMessage parent t3 =
  if eqb_la parent
       (list_ascii_of_string
         ('o'::('p'::('_'::('t'::('y'::('p'::('e'::[]))))))))
  then app
         (list_ascii_of_string
           ('E'::('r'::('r'::('o'::('r'::(' '::('2'::(':'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('"'::[])))))))))))))))))))))
         (app (node_value t3)
           (app
             (list_ascii_of_string
               ('"'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::(' '::('S'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('o'::('p'::('e'::('a'::('r'::('a'::('t'::('i'::('o'::('n'::('s'::(' '::('a'::('r'::('e'::(' '::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))
             (supportedValues parent)))
  else list_ascii_of_string
         ('E'::('r'::('r'::('o'::('r'::(' '::('0'::(':'::(' '::('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('e'::('r'::('r'::('o'::('r'::[]))))))))))))))))))))))

(** val append_option :
    'a1 error_option -> 'a1 list error_option -> 'a1 list error_option **)

let append_option a b =
  match a with
  | Success la ->
    (match b with
     | Success lb -> Success (la :: lb)
     | Error s0 -> Error s0)
  | Error s0 -> Error s0

(** val extract_error : tree error_option list -> tree list error_option **)

let rec extract_error = function
| [] -> Success []
| h :: t3 -> append_option h (extract_error t3)

(** val filter_recursive : char list -> tree -> tree error_option **)

let rec filter_recursive parent t3 = match t3 with
| Leaf value ->
  if attributesAcceptsValue parent value
  then Success (Leaf value)
  else Error (string_of_list_ascii (createWarningErrorMessage parent t3))
| Subtree (value, children) ->
  (match children with
   | [] ->
     if attributesAcceptsValue parent value
     then Success (Leaf value)
     else Error (string_of_list_ascii (createWarningErrorMessage parent t3))
   | _ :: _ ->
     let filtered_children = map (filter_recursive value) children in
     let error = extract_error filtered_children in
     (match error with
      | Success _ -> Success (Subtree (value, children))
      | Error s0 -> Error s0))

(** val filter0 : tree -> tree error_option **)

let filter0 t3 =
  filter_recursive (list_ascii_of_string ('m'::('a'::('i'::('n'::[]))))) t3

type 't fourtuple =
  (('t list * 't list) * 't list) * 't list
  (* singleton inductive, whose constructor was ft *)

(** val get_input : 'a1 fourtuple -> 'a1 list **)

let get_input t3 =
  fst (fst (fst t3))

(** val get_output : 'a1 fourtuple -> 'a1 list **)

let get_output t3 =
  snd (fst (fst t3))

(** val get_nodes : 'a1 fourtuple -> 'a1 list **)

let get_nodes t3 =
  snd (fst t3)

(** val get_initializer : 'a1 fourtuple -> 'a1 list **)

let get_initializer =
  snd

type iR_dim =
| Dim_scalar
| Dim_vector of nat
| Dim_matrix of nat * nat

type iR_fixedValue =
| Value of iR_dim * char list list

type iR_operation =
| Gemm of char list * char list * char list * char list
| Relu

type iR_elem =
| IR_input of char list * iR_dim
| IR_output of char list * iR_dim
| IR_node of char list * char list list * char list list * iR_operation
| IR_initializer of char list * iR_fixedValue

type nNPremodel =
| NNPremodel_initializer_matrix of char list * nat * nat
   * (nat -> nat -> char list)
| NNPremodel_initializer_vector of char list * nat * (nat -> char list)
| NNPremodel_Output of char list * nat
| NNPremodel_Linear of char list * char list * char list * char list
   * char list * char list
| NNPremodel_ReLu of char list * char list

(** val node_collector : tree -> tree fourtuple **)

let node_collector t3 =
  ((((grabAll
       (map list_ascii_of_string
         (('g'::('r'::('a'::('p'::('h'::[]))))) :: []))
       ('i'::('n'::('p'::('u'::('t'::[]))))) t3),
    (grabAll
      (map list_ascii_of_string (('g'::('r'::('a'::('p'::('h'::[]))))) :: []))
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))) t3)),
    (grabAll
      (map list_ascii_of_string (('g'::('r'::('a'::('p'::('h'::[]))))) :: []))
      ('n'::('o'::('d'::('e'::[])))) t3)),
    (grabAll
      (map list_ascii_of_string (('g'::('r'::('a'::('p'::('h'::[]))))) :: []))
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::[])))))))))))
      t3))

(** val nat_of_ascii1 : char -> nat option **)

let nat_of_ascii1 c =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then if b0
         then if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6
                                       then None
                                       else Some (S (S (S (S (S (S (S O)))))))
                             else None
                        else None
              else if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (S (S (S O)))
                             else None
                        else None
         else if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6
                                       then None
                                       else Some (S (S (S (S (S O)))))
                             else None
                        else None
              else if b2
                   then if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6
                                       then None
                                       else Some (S (S (S (S (S (S (S (S (S
                                              O)))))))))
                             else None
                        else None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (S O)
                             else None
                        else None
    else if b0
         then if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6
                                       then None
                                       else Some (S (S (S (S (S (S O))))))
                             else None
                        else None
              else if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (S (S O))
                             else None
                        else None
         else if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6
                                       then None
                                       else Some (S (S (S (S O))))
                             else None
                        else None
              else if b2
                   then if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6
                                       then None
                                       else Some (S (S (S (S (S (S (S (S
                                              O))))))))
                             else None
                        else None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some O
                             else None
                        else None)
    c

(** val nat_of_string_r : char list -> nat option **)

let rec nat_of_string_r = function
| [] -> Some O
| h :: t3 ->
  (match nat_of_ascii1 h with
   | Some n0 ->
     (match nat_of_string_r t3 with
      | Some m ->
        Some (add n0 (mul (S (S (S (S (S (S (S (S (S (S O)))))))))) m))
      | None -> None)
   | None -> None)

(** val nat_of_string : char list -> nat option **)

let nat_of_string s0 =
  nat_of_string_r (rev s0)

(** val append_option0 :
    'a1 error_option -> 'a1 list error_option -> 'a1 list error_option **)

let append_option0 a b =
  match a with
  | Success la ->
    (match b with
     | Success lb -> Success (la :: lb)
     | Error s0 -> Error s0)
  | Error s0 -> Error s0

(** val extract_error0 : 'a1 error_option list -> 'a1 list error_option **)

let rec extract_error0 = function
| [] -> Success []
| h :: t3 -> append_option0 h (extract_error0 t3)

(** val filter_some : 'a1 option list -> 'a1 list **)

let rec filter_some = function
| [] -> []
| h :: t3 ->
  (match h with
   | Some e -> e :: (filter_some t3)
   | None -> filter_some t3)

(** val convert_inputToDim : tree -> iR_dim error_option **)

let convert_inputToDim t3 =
  let tensor_type_option =
    grab
      (map list_ascii_of_string
        (('t'::('y'::('p'::('e'::[])))) :: (('t'::('e'::('n'::('s'::('o'::('r'::('_'::('t'::('y'::('p'::('e'::[]))))))))))) :: [])))
      t3
  in
  (match tensor_type_option with
   | Some tensor_type ->
     (match grab
              (map list_ascii_of_string
                (('s'::('h'::('a'::('p'::('e'::[]))))) :: (('d'::('i'::('m'::[]))) :: (('d'::('i'::('m'::('_'::('p'::('a'::('r'::('a'::('m'::[]))))))))) :: []))))
              tensor_type with
      | Some _ ->
        Error
          ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('n'::('a'::('m'::('e'::('s'::('p'::('a'::('c'::('e'::(' '::('S'::('h'::('a'::('p'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('\''::('d'::('i'::('m'::('_'::('p'::('a'::('r'::('a'::('m'::('\''::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::(' '::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('S'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('i'::('s'::(' '::('o'::('n'::('l'::('y'::(' '::('\''::('d'::('i'::('m'::('_'::('v'::('a'::('l'::('u'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | None ->
        let dim =
          grabAll
            (map list_ascii_of_string
              (('s'::('h'::('a'::('p'::('e'::[]))))) :: []))
            ('d'::('i'::('m'::[]))) tensor_type
        in
        let dim_values_options =
          map
            (grab
              (map list_ascii_of_string
                (('d'::('i'::('m'::('_'::('v'::('a'::('l'::('u'::('e'::[]))))))))) :: [])))
            dim
        in
        let dim_values = filter_some dim_values_options in
        (match dim_values with
         | [] -> Success Dim_scalar
         | h :: t4 ->
           (match t4 with
            | [] ->
              (match grab_value [] h with
               | Some grabbed ->
                 (match nat_of_string grabbed with
                  | Some n0 -> Success (Dim_vector n0)
                  | None ->
                    Error
                      ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('S'::('p'::('e'::('c'::('i'::('f'::('i'::('c'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('o'::('f'::(' '::('\''::('d'::('i'::('m'::('_'::('v'::('a'::('l'::('u'::('e'::('\''::(' '::('k'::('e'::('y'::(' '::('d'::('o'::('e'::('s'::('n'::('\''::('t'::(' '::('s'::('e'::('e'::('m'::(' '::('t'::('o'::(' '::('b'::('e'::(' '::('a'::(' '::('n'::('a'::('t'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
               | None ->
                 Error
                   ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('S'::('p'::('e'::('c'::('i'::('f'::('i'::('c'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('o'::('f'::(' '::('\''::('d'::('i'::('m'::('_'::('v'::('a'::('l'::('u'::('e'::('\''::(' '::('k'::('e'::('y'::(' '::('d'::('o'::('e'::('s'::('n'::('\''::('t'::(' '::('s'::('e'::('e'::('m'::(' '::('t'::('o'::(' '::('e'::('x'::('i'::('s'::('t'::(' '::('('::('t'::('r'::('i'::('e'::('d'::(' '::('t'::('o'::(' '::('b'::('u'::('i'::('l'::('d'::(' '::('v'::('e'::('c'::('t'::('o'::('r'::(')'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            | h2 :: l ->
              (match l with
               | [] ->
                 (match grab_value [] h with
                  | Some grabbed1 ->
                    (match nat_of_string grabbed1 with
                     | Some n1 ->
                       (match grab_value [] h2 with
                        | Some grabbed2 ->
                          (match nat_of_string grabbed2 with
                           | Some n2 -> Success (Dim_matrix (n1, n2))
                           | None ->
                             Error
                               ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('S'::('p'::('e'::('c'::('i'::('f'::('i'::('c'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('o'::('f'::(' '::('\''::('d'::('i'::('m'::('_'::('v'::('a'::('l'::('u'::('e'::('\''::(' '::('k'::('e'::('y'::(' '::('d'::('o'::('e'::('s'::('n'::('\''::('t'::(' '::('s'::('e'::('e'::('m'::(' '::('t'::('o'::(' '::('b'::('e'::(' '::('a'::(' '::('n'::('a'::('t'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        | None ->
                          Error
                            ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('S'::('p'::('e'::('c'::('i'::('f'::('i'::('c'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('o'::('f'::(' '::('\''::('d'::('i'::('m'::('_'::('v'::('a'::('l'::('u'::('e'::('\''::(' '::('k'::('e'::('y'::(' '::('d'::('o'::('e'::('s'::('n'::('\''::('t'::(' '::('s'::('e'::('e'::('m'::(' '::('t'::('o'::(' '::('e'::('x'::('i'::('s'::('t'::(' '::('('::('t'::('r'::('i'::('e'::('d'::(' '::('t'::('o'::(' '::('b'::('u'::('i'::('l'::('d'::(' '::('m'::('a'::('t'::('r'::('i'::('x'::(','::(' '::('2'::(')'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                     | None ->
                       Error
                         ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('S'::('p'::('e'::('c'::('i'::('f'::('i'::('c'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('o'::('f'::(' '::('\''::('d'::('i'::('m'::('_'::('v'::('a'::('l'::('u'::('e'::('\''::(' '::('k'::('e'::('y'::(' '::('d'::('o'::('e'::('s'::('n'::('\''::('t'::(' '::('s'::('e'::('e'::('m'::(' '::('t'::('o'::(' '::('b'::('e'::(' '::('a'::(' '::('n'::('a'::('t'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                  | None ->
                    Error
                      ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('S'::('p'::('e'::('c'::('i'::('f'::('i'::('c'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('o'::('f'::(' '::('\''::('d'::('i'::('m'::('_'::('v'::('a'::('l'::('u'::('e'::('\''::(' '::('k'::('e'::('y'::(' '::('d'::('o'::('e'::('s'::('n'::('\''::('t'::(' '::('s'::('e'::('e'::('m'::(' '::('t'::('o'::(' '::('e'::('x'::('i'::('s'::('t'::(' '::('('::('t'::('r'::('i'::('e'::('d'::(' '::('t'::('o'::(' '::('b'::('u'::('i'::('l'::('d'::(' '::('m'::('a'::('t'::('r'::('i'::('x'::(','::(' '::('1'::(')'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
               | _ :: _ ->
                 Error
                   ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('o'::('n'::('l'::('y'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('t'::('e'::('n'::('s'::('o'::('r'::(' '::('v'::('a'::('l'::('u'::('e'::('s'::(' '::('a'::('r'::('e'::(' '::('s'::('c'::('a'::('l'::('a'::('r'::('s'::(','::(' '::('v'::('e'::('c'::('t'::('o'::('r'::('s'::(' '::('a'::('n'::('d'::(' '::('m'::('a'::('t'::('r'::('i'::('c'::('e'::('s'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   | None ->
     Error
       ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('\''::('T'::('e'::('n'::('s'::('o'::('r'::('\''::(' '::('e'::('n'::('t'::('r'::('y'::(' '::('i'::('n'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('n'::('o'::('d'::('e'::('.'::(' '::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('P'::('l'::('e'::('a'::('s'::('e'::(' '::('n'::('o'::('t'::('e'::(' '::('t'::('h'::('a'::('t'::(' '::('\''::('S'::('e'::('q'::('u'::('e'::('n'::('c'::('e'::('\''::(','::(' '::('\''::('M'::('a'::('p'::('\''::(','::(' '::('\''::('O'::('p'::('t'::('i'::('o'::('n'::('a'::('l'::('\''::(' '::('a'::('n'::('d'::(' '::('\''::('S'::('p'::('a'::('r'::('s'::('e'::('T'::('e'::('n'::('s'::('o'::('r'::('\''::(' '::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('r'::('e'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('c'::('u'::('r'::('r'::('e'::('n'::('t'::('l'::('y'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('o'::('r'::(' '::('m'::('a'::('k'::('e'::(' '::('n'::('o'::(' '::('s'::('e'::('n'::('s'::('e'::(' '::('a'::('s'::(' '::('a'::(' '::('d'::('a'::('t'::('a'::(' '::('t'::('y'::('p'::('e'::(' '::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('o'::('f'::(' '::('a'::('n'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('n'::('o'::('d'::('e'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val convert_input : tree -> iR_elem error_option **)

let convert_input t3 =
  let name_option =
    grab_value
      (map list_ascii_of_string (('n'::('a'::('m'::('e'::[])))) :: [])) t3
  in
  (match name_option with
   | Some name ->
     let dim = convert_inputToDim t3 in
     (match dim with
      | Success irdim ->
        Success (IR_input ((string_of_list_ascii name), irdim))
      | Error s0 -> Error s0)
   | None ->
     Error
       ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('a'::('m'::('e'::(' '::('e'::('n'::('t'::('r'::('y'::(' '::('i'::('n'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('n'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))))))))

(** val convert_output : tree -> iR_elem error_option **)

let convert_output t3 =
  let name_option =
    grab_value
      (map list_ascii_of_string (('n'::('a'::('m'::('e'::[])))) :: [])) t3
  in
  (match name_option with
   | Some name ->
     let dim = convert_inputToDim t3 in
     (match dim with
      | Success irdim ->
        Success (IR_output ((string_of_list_ascii name), irdim))
      | Error s0 -> Error s0)
   | None ->
     Error
       ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('a'::('m'::('e'::(' '::('e'::('n'::('t'::('r'::('y'::(' '::('i'::('n'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('n'::('o'::('d'::('e'::[]))))))))))))))))))))))))))))))))))))))))))

(** val convert_attribute : tree -> char list error_option **)

let convert_attribute t3 =
  let type_option =
    grab_value
      (map list_ascii_of_string (('t'::('y'::('p'::('e'::[])))) :: [])) t3
  in
  (match type_option with
   | Some type0 ->
     (match string_of_list_ascii type0 with
      | [] ->
        Error
          ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then if b0
               then Error
                      ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
               else if b1
                    then Error
                           ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                    else if b2
                         then if b3
                              then Error
                                     ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                              else if b4
                                   then Error
                                          ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                   else if b5
                                        then if b6
                                             then Error
                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                             else (match s0 with
                                                   | [] ->
                                                     Error
                                                       ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then Error
                                                              ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                       else if b8
                                                            then if b9
                                                                 then 
                                                                   if b10
                                                                   then 
                                                                    if b11
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    let name_option =
                                                                    grab_value
                                                                    (map
                                                                    list_ascii_of_string
                                                                    (('n'::('a'::('m'::('e'::[])))) :: []))
                                                                    t3
                                                                    in
                                                                    (
                                                                    match name_option with
                                                                    | Some _ ->
                                                                    let i_option =
                                                                    grab_value
                                                                    (map
                                                                    list_ascii_of_string
                                                                    (('i'::[]) :: []))
                                                                    t3
                                                                    in
                                                                    (
                                                                    match i_option with
                                                                    | Some i ->
                                                                    Success
                                                                    (string_of_list_ascii
                                                                    i)
                                                                    | None ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('i'::(' '::('e'::('n'::('t'::('r'::('y'::(' '::('i'::('n'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('n'::('o'::('d'::('e'::[]))))))))))))))))))))))))))))))))))))))))))
                                                                    | None ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('a'::('m'::('e'::(' '::('e'::('n'::('t'::('r'::('y'::(' '::('i'::('n'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('n'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))
                                                                    | _::_ ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a1)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                   else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                 else 
                                                                   Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                            else Error
                                                                   ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                       a0)
                                        else Error
                                               ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                         else Error
                                ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
          else if b0
               then if b1
                    then if b2
                         then Error
                                ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                         else if b3
                              then Error
                                     ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                              else if b4
                                   then Error
                                          ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                   else if b5
                                        then if b6
                                             then Error
                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                             else (match s0 with
                                                   | [] ->
                                                     Error
                                                       ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                   | a0::s1 ->
                                                     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                       (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                       if b7
                                                       then Error
                                                              ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                       else if b8
                                                            then Error
                                                                   ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                            else if b9
                                                                 then 
                                                                   if b10
                                                                   then 
                                                                    if b11
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b26
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b27
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b32
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    if b36
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    let name_option =
                                                                    grab_value
                                                                    (map
                                                                    list_ascii_of_string
                                                                    (('n'::('a'::('m'::('e'::[])))) :: []))
                                                                    t3
                                                                    in
                                                                    (
                                                                    match name_option with
                                                                    | Some _ ->
                                                                    let f_option =
                                                                    grab_value
                                                                    (map
                                                                    list_ascii_of_string
                                                                    (('f'::[]) :: []))
                                                                    t3
                                                                    in
                                                                    (
                                                                    match f_option with
                                                                    | Some f ->
                                                                    Success
                                                                    (string_of_list_ascii
                                                                    f)
                                                                    | None ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('f'::(' '::('e'::('n'::('t'::('r'::('y'::(' '::('i'::('n'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('n'::('o'::('d'::('e'::[]))))))))))))))))))))))))))))))))))))))))))
                                                                    | None ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('a'::('m'::('e'::(' '::('e'::('n'::('t'::('r'::('y'::(' '::('i'::('n'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('n'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))
                                                                    | _::_ ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a3)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a2)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a1)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                   else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                 else 
                                                                   Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                       a0)
                                        else Error
                                               ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
                    else Error
                           ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
               else Error
                      ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('\''::('F'::('L'::('O'::('A'::('T'::('\''::(' '::('o'::('r'::(' '::('\''::('I'::('N'::('T'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
          a)
   | None ->
     Error
       ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('n'::('t'::('r'::('y'::(' '::('i'::('n'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('n'::('o'::('d'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))

(** val default_value : char list -> char list -> char list error_option **)

let default_value op_type attribute_name =
  match op_type with
  | [] ->
    Error
      ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | a::s0 ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b b0 b1 b2 b3 b4 b5 b6 ->
      if b
      then Error
             ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      else if b0
           then if b1
                then Error
                       ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                else if b2
                     then Error
                            ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                     else if b3
                          then Error
                                 ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                          else if b4
                               then if b5
                                    then Error
                                           ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    else if b6
                                         then Error
                                                ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                         else (match s0 with
                                               | [] ->
                                                 Error
                                                   ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                               | a0::s1 ->
                                                 (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                   (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                   if b7
                                                   then if b8
                                                        then if b9
                                                             then if b10
                                                                  then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                  else 
                                                                    if b11
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b40
                                                                    then 
                                                                    if b41
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b42
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b46
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    (match attribute_name with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a5::s6 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b47 b48 b49 b50 b51 b52 b53 b54 ->
                                                                    if b47
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b48
                                                                    then 
                                                                    if b49
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b50
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b51
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b52
                                                                    then 
                                                                    if b53
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b54
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s6 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a6::s7 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b55 b56 b57 b58 b59 b60 b61 b62 ->
                                                                    if b55
                                                                    then 
                                                                    if b56
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b58
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a7::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b64
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then 
                                                                    if b67
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b72
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b74
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b81
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b82
                                                                    then 
                                                                    if b83
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b89
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b90
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b91
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b98
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    if b101
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b102
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    Success
                                                                    ('1'::[])
                                                                    | _::_ ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a11)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a10)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a9)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a8)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a7)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b56
                                                                    then 
                                                                    if b57
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b58
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a7::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    if b64
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b65
                                                                    then 
                                                                    if b66
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b67
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b72
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    if b74
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    if b80
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b81
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b82
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b83
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b88
                                                                    then 
                                                                    if b89
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b90
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b91
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b94
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    Success
                                                                    ('1'::[])
                                                                    | _::_ ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a10)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a9)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a8)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a7)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b57
                                                                    then 
                                                                    if b58
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b59
                                                                    then 
                                                                    if b60
                                                                    then 
                                                                    if b61
                                                                    then 
                                                                    if b62
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s7 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a7::s8 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b63 b64 b65 b66 b67 b68 b69 b70 ->
                                                                    if b63
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b64
                                                                    then 
                                                                    if b65
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b66
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b67
                                                                    then 
                                                                    if b68
                                                                    then 
                                                                    if b69
                                                                    then 
                                                                    if b70
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s8 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a8::s9 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b71 b72 b73 b74 b75 b76 b77 b78 ->
                                                                    if b71
                                                                    then 
                                                                    if b72
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b73
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b74
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b75
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b76
                                                                    then 
                                                                    if b77
                                                                    then 
                                                                    if b78
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s9 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a9::s10 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b79 b80 b81 b82 b83 b84 b85 b86 ->
                                                                    if b79
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b80
                                                                    then 
                                                                    if b81
                                                                    then 
                                                                    if b82
                                                                    then 
                                                                    if b83
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b84
                                                                    then 
                                                                    if b85
                                                                    then 
                                                                    if b86
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s10 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a10::s11 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b87 b88 b89 b90 b91 b92 b93 b94 ->
                                                                    if b87
                                                                    then 
                                                                    if b88
                                                                    then 
                                                                    if b89
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b90
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b91
                                                                    then 
                                                                    if b92
                                                                    then 
                                                                    if b93
                                                                    then 
                                                                    if b94
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s11 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a11::s12 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b95 b96 b97 b98 b99 b100 b101 b102 ->
                                                                    if b95
                                                                    then 
                                                                    if b96
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b97
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b98
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b106
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b110
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    Success
                                                                    ('0'::[])
                                                                    | _::_ ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a12)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b96
                                                                    then 
                                                                    if b97
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b98
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b99
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b100
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b101
                                                                    then 
                                                                    if b102
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s12 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a12::s13 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b103 b104 b105 b106 b107 b108 b109 b110 ->
                                                                    if b103
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b104
                                                                    then 
                                                                    if b105
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b106
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b107
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b108
                                                                    then 
                                                                    if b109
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b110
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s13 with
                                                                    | [] ->
                                                                    Success
                                                                    ('0'::[])
                                                                    | _::_ ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a12)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a11)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a10)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a9)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a8)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a7)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a6)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('f'::('o'::('r'::(' '::('\''::('G'::('e'::('m'::('m'::('\''::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a5)
                                                                    | _::_ ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a4)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a3)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a2)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a1)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                             else Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                        else Error
                                                               ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                   else Error
                                                          ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                   a0)
                               else Error
                                      ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           else Error
                  ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('n'::('e'::('c'::('e'::('s'::('s'::('a'::('r'::('y'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('n'::('d'::(' '::('n'::('o'::(' '::('d'::('e'::('f'::('a'::('u'::('l'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('a'::(' '::('\''::('n'::('o'::('d'::('e'::('\''::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      a

(** val search_attribute :
    tree list -> char list -> char list -> char list error_option **)

let rec search_attribute l v op_type =
  match l with
  | [] -> default_value op_type v
  | h :: t3 ->
    let name_option =
      grab_value
        (map list_ascii_of_string (('n'::('a'::('m'::('e'::[])))) :: [])) h
    in
    (match name_option with
     | Some name ->
       if eqb0 (string_of_list_ascii name) v
       then convert_attribute h
       else search_attribute t3 v op_type
     | None -> search_attribute t3 v op_type)

(** val convert_gemm_attributes : tree -> iR_operation error_option **)

let convert_gemm_attributes t3 =
  let attributes =
    grabAll []
      ('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::[]))))))))) t3
  in
  (match search_attribute attributes
           ('"'::('a'::('l'::('p'::('h'::('a'::('"'::[])))))))
           ('"'::('G'::('e'::('m'::('m'::('"'::[])))))) with
   | Success alpha ->
     (match search_attribute attributes
              ('"'::('b'::('e'::('t'::('a'::('"'::[]))))))
              ('"'::('G'::('e'::('m'::('m'::('"'::[])))))) with
      | Success beta ->
        (match search_attribute attributes
                 ('"'::('t'::('r'::('a'::('n'::('s'::('A'::('"'::[]))))))))
                 ('"'::('G'::('e'::('m'::('m'::('"'::[])))))) with
         | Success transA ->
           (match search_attribute attributes
                    ('"'::('t'::('r'::('a'::('n'::('s'::('B'::('"'::[]))))))))
                    ('"'::('G'::('e'::('m'::('m'::('"'::[])))))) with
            | Success transB -> Success (Gemm (alpha, beta, transA, transB))
            | Error s0 -> Error s0)
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | Error s0 -> Error s0)

(** val convert_node : tree -> iR_elem error_option **)

let convert_node t3 =
  let name =
    grab_value
      (map list_ascii_of_string (('n'::('a'::('m'::('e'::[])))) :: [])) t3
  in
  (match name with
   | Some name0 ->
     let inputs = grabAll [] ('i'::('n'::('p'::('u'::('t'::[]))))) t3 in
     (match inputs with
      | [] ->
        Error
          ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('i'::('n'::(' '::('n'::('o'::('d'::('e'::('.'::[]))))))))))))))))))))))))))))))
      | _ :: _ ->
        let input_list = filter_some (map (grab_value []) inputs) in
        let outputs =
          grabAll [] ('o'::('u'::('t'::('p'::('u'::('t'::[])))))) t3
        in
        (match outputs with
         | [] ->
           Error
             ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('i'::('n'::(' '::('n'::('o'::('d'::('e'::('.'::[])))))))))))))))))))))))))))))))
         | _ :: _ ->
           let output_list = filter_some (map (grab_value []) outputs) in
           let op_type_option =
             grab_value
               (map list_ascii_of_string
                 (('o'::('p'::('_'::('t'::('y'::('p'::('e'::[]))))))) :: []))
               t3
           in
           (match op_type_option with
            | Some op_type ->
              (match string_of_list_ascii op_type with
               | [] ->
                 Error
                   ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
               | a::s0 ->
                 (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                   (fun b b0 b1 b2 b3 b4 b5 b6 ->
                   if b
                   then Error
                          ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   else if b0
                        then if b1
                             then Error
                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                             else if b2
                                  then Error
                                         ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  else if b3
                                       then Error
                                              ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       else if b4
                                            then if b5
                                                 then Error
                                                        ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                 else if b6
                                                      then Error
                                                             ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                      else (match s0 with
                                                            | [] ->
                                                              Error
                                                                ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                            | a0::s1 ->
                                                              (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                                if b7
                                                                then 
                                                                  if b8
                                                                  then 
                                                                    if b9
                                                                    then 
                                                                    if b10
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b11
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    if b24
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    if b35
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b40
                                                                    then 
                                                                    if b41
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b42
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b46
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    let attributes =
                                                                    convert_gemm_attributes
                                                                    t3
                                                                    in
                                                                    (
                                                                    match attributes with
                                                                    | Success operation ->
                                                                    Success
                                                                    (IR_node
                                                                    ((string_of_list_ascii
                                                                    name0),
                                                                    (map
                                                                    string_of_list_ascii
                                                                    input_list),
                                                                    (map
                                                                    string_of_list_ascii
                                                                    output_list),
                                                                    operation))
                                                                    | Error s6 ->
                                                                    Error s6)
                                                                    | _::_ ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a4)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a3)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a2)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a1)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                  else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                else 
                                                                  if b8
                                                                  then 
                                                                    if b9
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b10
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    if b18
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a2::s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s3 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a3::s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then 
                                                                    if b32
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s4 with
                                                                    | [] ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | a4::s5 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b39 b40 b41 b42 b43 b44 b45 b46 ->
                                                                    if b39
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b40
                                                                    then 
                                                                    if b41
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b42
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b43
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b44
                                                                    then 
                                                                    if b45
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b46
                                                                    then 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s5 with
                                                                    | [] ->
                                                                    Success
                                                                    (IR_node
                                                                    ((string_of_list_ascii
                                                                    name0),
                                                                    (map
                                                                    string_of_list_ascii
                                                                    input_list),
                                                                    (map
                                                                    string_of_list_ascii
                                                                    output_list),
                                                                    Relu))
                                                                    | _::_ ->
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a4)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a3)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a2)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    a1)
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                  else 
                                                                    Error
                                                                    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                a0)
                                            else Error
                                                   ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        else Error
                               ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('r'::('b'::('i'::('d'::('d'::('e'::('n'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('s'::('h'::('o'::('u'::('l'::('d'::(' '::('h'::('a'::('v'::('e'::(' '::('b'::('e'::('e'::('n'::(' '::('r'::('e'::('m'::('o'::('v'::('e'::('d'::(' '::('b'::('y'::(' '::('t'::('h'::('e'::(' '::('f'::('i'::('l'::('t'::('e'::('r'::('.'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('y'::('o'::('u'::(' '::('a'::('r'::('e'::(' '::('u'::('s'::('i'::('n'::('g'::(' '::('a'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   a)
            | None ->
              Error
                ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('\''::('o'::('p'::('_'::('t'::('y'::('p'::('e'::('\''::(' '::('v'::('a'::('l'::('u'::('e'::('.'::[])))))))))))))))))))))))))))))))))))
   | None ->
     Error
       ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('n'::('o'::(' '::('\''::('n'::('a'::('m'::('e'::('\''::(' '::('i'::('n'::(' '::('n'::('o'::('d'::('e'::('.'::[]))))))))))))))))))))))))))))))))

(** val extract_data_converted : tree -> char list list **)

let extract_data_converted t3 =
  map string_of_list_ascii
    (filter_some
      (map (grab_value [])
        (grabAll []
          ('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('d'::[]))))))))))))))
          t3)))

(** val data_extraction_list : (tree -> char list list) list **)

let data_extraction_list =
  extract_data_converted :: []

(** val extract_data :
    tree -> nat -> (tree -> char list list) list -> char list list option **)

let rec extract_data t3 expected_length = function
| [] -> None
| h :: tail ->
  let call0 = h t3 in
  if eqb (length call0) expected_length
  then Some call0
  else extract_data t3 expected_length tail

(** val convert_IR_fixedValue : tree -> iR_fixedValue error_option **)

let convert_IR_fixedValue t3 =
  let dims =
    filter_some
      (map nat_of_string
        (filter_some
          (map (grab_value []) (grabAll [] ('d'::('i'::('m'::('s'::[])))) t3))))
  in
  (match dims with
   | [] ->
     let data = extract_data t3 (S O) data_extraction_list in
     (match data with
      | Some l -> Success (Value (Dim_scalar, l))
      | None ->
        Error
          ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('C'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::(' '::('d'::('a'::('t'::('a'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::(' '::('n'::('o'::('d'::('e'::('.'::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('t'::('h'::('e'::(' '::('t'::('y'::('p'::('e'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('o'::('r'::(' '::('y'::('o'::('u'::(' '::('f'::('o'::('r'::('g'::('o'::('t'::(' '::('t'::('o'::(' '::('r'::('u'::('n'::(' '::('\''::('r'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::('.'::('p'::('y'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   | n0 :: l ->
     (match l with
      | [] ->
        let data = extract_data t3 n0 data_extraction_list in
        (match data with
         | Some l0 -> Success (Value ((Dim_vector n0), l0))
         | None ->
           Error
             ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('C'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::(' '::('d'::('a'::('t'::('a'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::(' '::('n'::('o'::('d'::('e'::('.'::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('t'::('h'::('e'::(' '::('t'::('y'::('p'::('e'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('o'::('r'::(' '::('y'::('o'::('u'::(' '::('f'::('o'::('r'::('g'::('o'::('t'::(' '::('t'::('o'::(' '::('r'::('u'::('n'::(' '::('\''::('r'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::('.'::('p'::('y'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | m :: l0 ->
        (match l0 with
         | [] ->
           let data = extract_data t3 (mul n0 m) data_extraction_list in
           (match data with
            | Some l1 -> Success (Value ((Dim_matrix (n0, m)), l1))
            | None ->
              Error
                ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('C'::('o'::('u'::('l'::('d'::(' '::('n'::('o'::('t'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::(' '::('d'::('a'::('t'::('a'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::(' '::('n'::('o'::('d'::('e'::('.'::(' '::('M'::('a'::('y'::('b'::('e'::(' '::('t'::('h'::('e'::(' '::('t'::('y'::('p'::('e'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::(' '::('o'::('r'::(' '::('y'::('o'::('u'::(' '::('f'::('o'::('r'::('g'::('o'::('t'::(' '::('t'::('o'::(' '::('r'::('u'::('n'::(' '::('\''::('r'::('a'::('w'::('_'::('d'::('a'::('t'::('a'::('_'::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('e'::('r'::('.'::('p'::('y'::('\''::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         | _ :: _ ->
           Error
             ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::(' '::('n'::('o'::('d'::('e'::(' '::('d'::('a'::('t'::('a'::(' '::('o'::('f'::(' '::('t'::('y'::('p'::('e'::(' '::('t'::('e'::('n'::('s'::('o'::('r'::(','::(' '::('w'::('h'::('i'::('c'::('h'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('s'::('c'::('a'::('l'::('a'::('r'::(','::(' '::('v'::('e'::('c'::('t'::('o'::('r'::(' '::('o'::('r'::(' '::('m'::('a'::('t'::('r'::('i'::('x'::('.'::(' '::('P'::('l'::('e'::('a'::('s'::('e'::(' '::('n'::('o'::('t'::('e'::(' '::('t'::('h'::('a'::('t'::(' '::('t'::('h'::('i'::('s'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val convert_initializer : tree -> iR_elem error_option **)

let convert_initializer t3 =
  let name_option =
    grab_value
      (map list_ascii_of_string (('n'::('a'::('m'::('e'::[])))) :: [])) t3
  in
  (match name_option with
   | Some name ->
     let fixed_value = convert_IR_fixedValue t3 in
     (match fixed_value with
      | Success v -> Success (IR_initializer ((string_of_list_ascii name), v))
      | Error s0 -> Error s0)
   | None ->
     Error
       ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('a'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::(' '::('n'::('o'::('d'::('e'::(' '::('d'::('o'::('e'::('s'::(' '::('n'::('o'::('t'::(' '::('d'::('e'::('f'::('i'::('n'::('e'::(' '::('a'::(' '::('n'::('a'::('m'::('e'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))

(** val iR_converter : tree fourtuple -> iR_elem fourtuple error_option **)

let iR_converter t3 =
  let input_list_option = extract_error0 (map convert_input (get_input t3)) in
  (match input_list_option with
   | Success input_list ->
     let output_list_option =
       extract_error0 (map convert_output (get_output t3))
     in
     (match output_list_option with
      | Success output_list ->
        let node_list_option =
          extract_error0 (map convert_node (get_nodes t3))
        in
        (match node_list_option with
         | Success node_list ->
           let initializer_list_option =
             extract_error0 (map convert_initializer (get_initializer t3))
           in
           (match initializer_list_option with
            | Success initializer_list ->
              Success (((input_list, output_list), node_list),
                initializer_list)
            | Error s0 -> Error s0)
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | Error s0 -> Error s0)

(** val getIndex_optionZero : char list list -> nat -> char list **)

let rec getIndex_optionZero l i =
  match l with
  | [] -> '0'::('.'::('0'::[]))
  | h :: t3 -> (match i with
                | O -> h
                | S n0 -> getIndex_optionZero t3 n0)

(** val get_value_matrix_list_optionZero :
    nat -> char list list -> nat -> nat -> char list **)

let get_value_matrix_list_optionZero w l m n0 =
  getIndex_optionZero l (add (mul n0 w) m)

(** val get_value_vector_list_optionZero :
    char list list -> nat -> char list **)

let get_value_vector_list_optionZero =
  getIndex_optionZero

(** val iR_fixedValue_matrix_to_function :
    iR_fixedValue -> (nat -> nat -> char list) option **)

let iR_fixedValue_matrix_to_function = function
| Value (dim, value_list) ->
  (match dim with
   | Dim_matrix (_, y) -> Some (get_value_matrix_list_optionZero y value_list)
   | _ -> None)

(** val iR_fixedValue_vector_to_function :
    iR_fixedValue -> (nat -> char list) option **)

let iR_fixedValue_vector_to_function = function
| Value (dim, value_list) ->
  (match dim with
   | Dim_vector _ -> Some (get_value_vector_list_optionZero value_list)
   | _ -> None)

(** val iR_initializer__to__NNPremodel_IR__initializers :
    iR_elem -> nNPremodel error_option **)

let iR_initializer__to__NNPremodel_IR__initializers = function
| IR_initializer (s0, fv) ->
  let Value (dim, _) = fv in
  (match dim with
   | Dim_scalar ->
     Error
       (append
         ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('s'::('c'::('a'::('l'::('a'::('r'::(' '::('i'::('n'::(' '::[]))))))))))))))))))
         (append s0
           ('.'::(' '::('W'::('e'::('i'::('g'::('h'::('t'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('m'::('a'::('t'::('r'::('i'::('c'::('e'::('s'::(','::(' '::('b'::('i'::('a'::('s'::('s'::('e'::('s'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('v'::('e'::('c'::('o'::('t'::('o'::('r'::('s'::(' '::('i'::('n'::(' '::('t'::('h'::('i'::('s'::(' '::('m'::('o'::('d'::('e'::('l'::('l'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   | Dim_vector n0 ->
     (match iR_fixedValue_vector_to_function fv with
      | Some function0 ->
        Success (NNPremodel_initializer_vector (s0, n0, function0))
      | None ->
        Error
          (append
            ('E'::('r'::('r'::('o'::('r'::(' '::('i'::('n'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('n'::('g'::(' '::[]))))))))))))))))))))
            (append s0
              (' '::('t'::('o'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::('.'::[]))))))))))))))))
   | Dim_matrix (n0, m) ->
     (match iR_fixedValue_matrix_to_function fv with
      | Some function0 ->
        Success (NNPremodel_initializer_matrix (s0, n0, m, function0))
      | None ->
        Error
          (append
            ('E'::('r'::('r'::('o'::('r'::(' '::('i'::('n'::(' '::('c'::('o'::('n'::('v'::('e'::('r'::('t'::('i'::('n'::('g'::(' '::[]))))))))))))))))))))
            (append s0
              (' '::('t'::('o'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::('.'::[])))))))))))))))))
| _ ->
  Error
    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('s'::('o'::('m'::('e'::(' '::('n'::('o'::('n'::('-'::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('i'::('n'::('i'::('t'::('i'::('a'::('l'::('i'::('z'::('e'::('r'::(' '::('l'::('i'::('s'::('t'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('m'::('i'::('g'::('h'::('t'::(' '::('b'::('e'::(' '::('a'::('n'::(' '::('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('e'::('r'::('r'::('o'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val iR_node__to__NNPremodel_IR : iR_elem -> nNPremodel error_option **)

let iR_node__to__NNPremodel_IR = function
| IR_node (_, li, lo, op) ->
  (match op with
   | Gemm (alpha, beta, transA, transB) ->
     (match alpha with
      | [] ->
        Error
          ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | a::s0 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b b0 b1 b2 b3 b4 b5 b6 ->
          if b
          then if b0
               then Error
                      ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
               else if b1
                    then Error
                           ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    else if b2
                         then Error
                                ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                         else if b3
                              then if b4
                                   then if b5
                                        then Error
                                               ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        else if b6
                                             then Error
                                                    ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                             else (match s0 with
                                                   | [] ->
                                                     (match transA with
                                                      | [] ->
                                                        Error
                                                          ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                      | a0::s1 ->
                                                        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                          (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                          if b7
                                                          then Error
                                                                 ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                          else if b8
                                                               then Error
                                                                    ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                               else if b9
                                                                    then 
                                                                    Error
                                                                    ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b10
                                                                    then 
                                                                    Error
                                                                    ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    Error
                                                                    ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    Error
                                                                    ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    (match li with
                                                                    | [] ->
                                                                    Error
                                                                    ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('g'::('e'::('m'::('m'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::('s'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | input :: l ->
                                                                    (match l with
                                                                    | [] ->
                                                                    Error
                                                                    ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('g'::('e'::('m'::('m'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::('s'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | weight :: l0 ->
                                                                    (match l0 with
                                                                    | [] ->
                                                                    Error
                                                                    ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('g'::('e'::('m'::('m'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::('s'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | bias :: l1 ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    (match lo with
                                                                    | [] ->
                                                                    Error
                                                                    ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('g'::('e'::('m'::('m'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::('s'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | output :: l2 ->
                                                                    (match l2 with
                                                                    | [] ->
                                                                    Success
                                                                    (NNPremodel_Linear
                                                                    (input,
                                                                    output,
                                                                    weight,
                                                                    bias,
                                                                    transB,
                                                                    beta))
                                                                    | _ :: _ ->
                                                                    Error
                                                                    ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('g'::('e'::('m'::('m'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::('s'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | _ :: _ ->
                                                                    Error
                                                                    ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('g'::('e'::('m'::('m'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('h'::('r'::('e'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::('s'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    | _::_ ->
                                                                    Error
                                                                    ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    else 
                                                                    Error
                                                                    ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                          a0)
                                                   | _::_ ->
                                                     Error
                                                       ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                   else Error
                                          ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                              else Error
                                     ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          else Error
                 ('A'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('a'::('l'::('p'::('h'::('a'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('m'::('u'::('s'::('t'::(' '::('b'::('e'::(' '::('1'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::(' '::('A'::('N'::('D'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::(' '::('t'::('r'::('a'::('n'::('s'::('A'::(' '::('o'::('f'::(' '::('g'::('e'::('m'::('m'::(' '::('o'::('p'::('e'::('r'::('a'::('t'::('i'::('o'::('n'::(' '::('b'::('e'::(' '::('0'::(' '::('o'::('r'::(' '::('N'::('o'::('n'::('e'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          a)
   | Relu ->
     (match li with
      | [] ->
        Error
          ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('r'::('e'::('l'::('u'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('o'::('n'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | input :: l ->
        (match l with
         | [] ->
           (match lo with
            | [] ->
              Error
                ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('r'::('e'::('l'::('u'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('o'::('n'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            | output :: l0 ->
              (match l0 with
               | [] -> Success (NNPremodel_ReLu (input, output))
               | _ :: _ ->
                 Error
                   ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('r'::('e'::('l'::('u'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('o'::('n'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         | _ :: _ ->
           Error
             ('F'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::('r'::('e'::('l'::('u'::(' '::('n'::('o'::('d'::('e'::(' '::('w'::('i'::('t'::('h'::(' '::('n'::('o'::('t'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('o'::('n'::('e'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('a'::('n'::('d'::(' '::('o'::('n'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| _ ->
  Error
    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('s'::('o'::('m'::('e'::(' '::('n'::('o'::('n'::('-'::('n'::('o'::('d'::('e'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('n'::('o'::('d'::('e'::(' '::('l'::('i'::('s'::('t'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('m'::('i'::('g'::('h'::('t'::(' '::('b'::('e'::(' '::('a'::('n'::(' '::('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('e'::('r'::('r'::('o'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val iR_output__to__NNPremodel_IR : iR_elem -> nNPremodel error_option **)

let iR_output__to__NNPremodel_IR = function
| IR_output (s0, dim) ->
  (match dim with
   | Dim_scalar ->
     Error
       ('T'::('h'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('d'::('i'::('m'::(' '::('c'::('a'::('n'::('t'::(' '::('b'::('e'::(' '::('a'::(' '::('s'::('c'::('a'::('l'::('a'::('r'::(' '::('i'::('n'::(' '::('t'::('h'::('i'::('s'::(' '::('m'::('o'::('d'::('e'::('l'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))
   | Dim_vector n0 -> Success (NNPremodel_Output (s0, n0))
   | Dim_matrix (n0, m) ->
     (match n0 with
      | O ->
        (match m with
         | O ->
           Error
             ('T'::('h'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('d'::('i'::('m'::(' '::('c'::('a'::('n'::('t'::(' '::('b'::('e'::(' '::('a'::(' '::('m'::('a'::('t'::('r'::('i'::('x'::(' '::('i'::('n'::(' '::('t'::('h'::('i'::('s'::(' '::('m'::('o'::('d'::('e'::('l'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))
         | S n1 ->
           (match n1 with
            | O -> Success (NNPremodel_Output (s0, n0))
            | S _ ->
              Error
                ('T'::('h'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('d'::('i'::('m'::(' '::('c'::('a'::('n'::('t'::(' '::('b'::('e'::(' '::('a'::(' '::('m'::('a'::('t'::('r'::('i'::('x'::(' '::('i'::('n'::(' '::('t'::('h'::('i'::('s'::(' '::('m'::('o'::('d'::('e'::('l'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))
      | S n1 ->
        (match n1 with
         | O -> Success (NNPremodel_Output (s0, m))
         | S _ ->
           (match m with
            | O ->
              Error
                ('T'::('h'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('d'::('i'::('m'::(' '::('c'::('a'::('n'::('t'::(' '::('b'::('e'::(' '::('a'::(' '::('m'::('a'::('t'::('r'::('i'::('x'::(' '::('i'::('n'::(' '::('t'::('h'::('i'::('s'::(' '::('m'::('o'::('d'::('e'::('l'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))
            | S n2 ->
              (match n2 with
               | O -> Success (NNPremodel_Output (s0, n0))
               | S _ ->
                 Error
                   ('T'::('h'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('d'::('i'::('m'::(' '::('c'::('a'::('n'::('t'::(' '::('b'::('e'::(' '::('a'::(' '::('m'::('a'::('t'::('r'::('i'::('x'::(' '::('i'::('n'::(' '::('t'::('h'::('i'::('s'::(' '::('m'::('o'::('d'::('e'::('l'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))
| _ ->
  Error
    ('E'::('r'::('r'::('o'::('r'::(':'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('s'::('o'::('m'::('e'::(' '::('n'::('o'::('n'::('-'::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('v'::('a'::('l'::('u'::('e'::(' '::('i'::('n'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('l'::('i'::('s'::('t'::('.'::(' '::('T'::('h'::('i'::('s'::(' '::('m'::('i'::('g'::('h'::('t'::(' '::('b'::('e'::(' '::('a'::('n'::(' '::('i'::('m'::('p'::('l'::('e'::('m'::('e'::('n'::('t'::('a'::('t'::('i'::('o'::('n'::(' '::('e'::('r'::('r'::('o'::('r'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val premodel_converter :
    iR_elem fourtuple -> nNPremodel list error_option **)

let premodel_converter ft =
  let inits = get_initializer ft in
  let nodes = get_nodes ft in
  let outputs = get_output ft in
  let error_option_inits =
    extract_error0 (map iR_initializer__to__NNPremodel_IR__initializers inits)
  in
  let error_option_nodes =
    extract_error0 (map iR_node__to__NNPremodel_IR nodes)
  in
  let error_option_outputs =
    extract_error0 (map iR_output__to__NNPremodel_IR outputs)
  in
  (match error_option_inits with
   | Success just_success_inits ->
     (match error_option_nodes with
      | Success just_success_nodes ->
        (match error_option_outputs with
         | Success just_success_outputs ->
           Success
             (app just_success_inits
               (app (rev just_success_outputs) (rev just_success_nodes)))
         | Error s0 -> Error s0)
      | Error s0 -> Error s0)
   | Error s0 -> Error s0)

(** val enlargeAsciiByOne : char -> (bool * char) option **)

let enlargeAsciiByOne a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then if b0
         then if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (false, '8')
                             else None
                        else None
              else if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (false, '4')
                             else None
                        else None
         else if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (false, '6')
                             else None
                        else None
              else if b2
                   then if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (true, '0')
                             else None
                        else None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (false, '2')
                             else None
                        else None
    else if b0
         then if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (false, '7')
                             else None
                        else None
              else if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (false, '3')
                             else None
                        else None
         else if b1
              then if b2
                   then None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (false, '5')
                             else None
                        else None
              else if b2
                   then if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (false, '9')
                             else None
                        else None
                   else if b3
                        then if b4
                             then if b5
                                  then None
                                  else if b6 then None else Some (false, '1')
                             else None
                        else None)
    a

(** val enlargeFlippedStringNumberByOneRec : char list -> char list **)

let rec enlargeFlippedStringNumberByOneRec = function
| [] -> list_ascii_of_string ('1'::[])
| h :: t3 ->
  (match enlargeAsciiByOne h with
   | Some p ->
     let (overflow, a) = p in
     if overflow
     then a :: (enlargeFlippedStringNumberByOneRec t3)
     else a :: t3
   | None -> list_ascii_of_string ('N'::('a'::('N'::[]))))

(** val enlargeStringNumberByOne : char list -> char list **)

let enlargeStringNumberByOne s0 =
  string_of_list_ascii
    (rev (enlargeFlippedStringNumberByOneRec (rev (list_ascii_of_string s0))))

(** val stringifyNat : nat -> char list **)

let rec stringifyNat = function
| O -> '0'::[]
| S n1 -> enlargeStringNumberByOne (stringifyNat n1)

(** val strigifyFunction_NatNatString_recXY :
    (nat -> nat -> char list) -> nat -> nat -> char list **)

let strigifyFunction_NatNatString_recXY f x y =
  append ('|'::(' '::[]))
    (append (stringifyNat x)
      (append (','::(' '::[]))
        (append (stringifyNat y)
          (append
            (' '::('='::('>'::(' '::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))
            (append (f x y)
              ('"'::('%'::('s'::('t'::('r'::('i'::('n'::('g'::('\n'::(' '::(' '::[]))))))))))))))))

(** val strigifyFunction_NatString_recX :
    (nat -> char list) -> nat -> char list **)

let strigifyFunction_NatString_recX f x =
  append ('|'::(' '::[]))
    (append (stringifyNat x)
      (append
        (' '::('='::('>'::(' '::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))
        (append (f x)
          ('"'::('%'::('s'::('t'::('r'::('i'::('n'::('g'::('\n'::(' '::(' '::[]))))))))))))))

(** val strigifyFunction_NatNatString_recY :
    (nat -> nat -> char list) -> nat -> nat -> char list **)

let rec strigifyFunction_NatNatString_recY f x y = match y with
| O -> strigifyFunction_NatNatString_recXY f x y
| S ylower ->
  append (strigifyFunction_NatNatString_recXY f x y)
    (strigifyFunction_NatNatString_recY f x ylower)

(** val strigifyFunction_NatNatString_recX :
    (nat -> nat -> char list) -> nat -> nat -> char list **)

let rec strigifyFunction_NatNatString_recX f x y =
  match x with
  | O ->
    append (strigifyFunction_NatNatString_recY f x y)
      ('|'::(' '::('_'::(','::(' '::('_'::(' '::('='::('>'::(' '::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::('0'::('.'::('0'::('"'::('%'::('s'::('t'::('r'::('i'::('n'::('g'::('\n'::(' '::(' '::[]))))))))))))))))))))))))))))))))))))))))
  | S xlower ->
    append (strigifyFunction_NatNatString_recY f x y)
      (strigifyFunction_NatNatString_recX f xlower y)

(** val strigifyFunction_NatString_rec :
    (nat -> char list) -> nat -> char list **)

let rec strigifyFunction_NatString_rec f x = match x with
| O ->
  append (strigifyFunction_NatString_recX f x)
    ('|'::(' '::('_'::(' '::('='::('>'::(' '::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::('0'::('.'::('0'::('"'::('%'::('s'::('t'::('r'::('i'::('n'::('g'::('\n'::(' '::(' '::[])))))))))))))))))))))))))))))))))))))
| S xlower ->
  append (strigifyFunction_NatString_recX f x)
    (strigifyFunction_NatString_rec f xlower)

(** val strigifyFunction_NatNatString :
    (nat -> nat -> char list) -> nat -> nat -> char list **)

let strigifyFunction_NatNatString f x _ =
  append
    ('('::('f'::('u'::('n'::(' '::('x'::(' '::('y'::(':'::(' '::('n'::('a'::('t'::(' '::('='::('>'::('\n'::(' '::(' '::(' '::('m'::('a'::('t'::('c'::('h'::(' '::('x'::(','::(' '::('y'::(' '::('w'::('i'::('t'::('h'::('\n'::(' '::(' '::[]))))))))))))))))))))))))))))))))))))))
    (append
      (strigifyFunction_NatNatString_recX f (sub x (S O)) (sub x (S O)))
      ('e'::('n'::('d'::(')'::('\n'::(' '::(' '::[]))))))))

(** val strigifyFunction_NatString :
    (nat -> char list) -> nat -> char list **)

let strigifyFunction_NatString f x =
  append
    ('('::('f'::('u'::('n'::(' '::('x'::(':'::(' '::('n'::('a'::('t'::(' '::('='::('>'::('\n'::(' '::(' '::(' '::('m'::('a'::('t'::('c'::('h'::(' '::('x'::(' '::('w'::('i'::('t'::('h'::('\n'::(' '::(' '::[])))))))))))))))))))))))))))))))))
    (append (strigifyFunction_NatString_rec f (sub x (S O)))
      ('e'::('n'::('d'::(')'::('\n'::(' '::(' '::[]))))))))

(** val replace : char list -> char -> char list -> char list **)

let rec replace s0 a r =
  match s0 with
  | [] -> []
  | c::rest ->
    if (=) c a then append r (replace rest a r) else c::(replace rest a r)

(** val replaceString : char list -> char list -> char list -> char list **)

let rec replaceString s0 s1 s2 =
  let len = length0 s1 in
  (match s0 with
   | [] -> []
   | c::rest ->
     if eqb0 s1 (substring O len s0)
     then append s2 (substring len (length0 s0) s0)
     else c::(replaceString rest s1 s2))

(** val remove : char list -> char -> char list **)

let rec remove s0 a =
  match s0 with
  | [] -> []
  | c::rest -> if (=) c a then remove rest a else c::(remove rest a)

(** val makeName : char list -> char list **)

let makeName s0 =
  replace
    (replace
      (replace
        (replace
          (replace
            (replace
              (replace
                (replace
                  (replace
                    (replace
                      (remove (remove (remove (remove s0 '"') '\'') '.') ':')
                      '0' ('_'::('z'::('e'::('r'::('o'::('_'::[]))))))) '1'
                    ('_'::('o'::('n'::('e'::('_'::[])))))) '2'
                  ('_'::('t'::('w'::('o'::('_'::[])))))) '3'
                ('_'::('t'::('h'::('r'::('e'::('e'::('_'::[])))))))) '4'
              ('_'::('f'::('o'::('u'::('r'::('_'::[]))))))) '5'
            ('_'::('f'::('i'::('v'::('e'::('_'::[]))))))) '6'
          ('_'::('s'::('i'::('x'::('_'::[])))))) '7'
        ('_'::('s'::('e'::('v'::('e'::('n'::('_'::[])))))))) '8'
      ('_'::('e'::('i'::('g'::('h'::('t'::('_'::[])))))))) '9'
    ('_'::('n'::('i'::('n'::('e'::('_'::[]))))))

(** val stringifyNNPremodel : nNPremodel -> char list **)

let stringifyNNPremodel = function
| NNPremodel_initializer_matrix (name, n0, m, function0) ->
  append
    ('D'::('e'::('f'::('i'::('n'::('i'::('t'::('i'::('o'::('n'::(' '::[])))))))))))
    (append (makeName name)
      (append
        (' '::(':'::('='::(' '::('m'::('k'::('_'::('m'::('a'::('t'::('r'::('i'::('x'::(' '::[]))))))))))))))
        (append (stringifyNat m)
          (append (' '::[])
            (append (stringifyNat n0)
              (append (' '::[])
                (append (strigifyFunction_NatNatString function0 m n0)
                  ('.'::[]))))))))
| NNPremodel_initializer_vector (name, n0, function0) ->
  append
    ('D'::('e'::('f'::('i'::('n'::('i'::('t'::('i'::('o'::('n'::(' '::[])))))))))))
    (append (makeName name)
      (append
        (' '::(':'::('='::(' '::('m'::('k'::('_'::('c'::('o'::('l'::('v'::('e'::('c'::(' '::[]))))))))))))))
        (append (stringifyNat n0)
          (append (' '::[])
            (append (strigifyFunction_NatString function0 n0) ('.'::[]))))))
| NNPremodel_Output (_, _) -> []
| NNPremodel_Linear (name, next, weight, bias, transB, beta) ->
  let weight_prefix =
    match transB with
    | [] ->
      '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
    | a::s0 ->
      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
        (fun b b0 b1 b2 b3 b4 b5 b6 ->
        if b
        then '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
        else if b0
             then '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
             else if b1
                  then '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                  else if b2
                       then '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                       else if b3
                            then if b4
                                 then if b5
                                      then '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                      else if b6
                                           then '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                           else (match s0 with
                                                 | [] ->
                                                   '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                 | a0::s1 ->
                                                   (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                     (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                     if b7
                                                     then '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                     else if b8
                                                          then if b9
                                                               then if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    if b22
                                                                    then 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    (match s2 with
                                                                    | [] -> []
                                                                    | _::_ ->
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[])))))))))))
                                                                    else 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[])))))))))))
                                                                    a1)
                                                                    else 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                                    else 
                                                                    '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                               else '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                                                          else '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[])))))))))))
                                                     a0)
                                 else '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[]))))))))))
                            else '('::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::(' '::[])))))))))))
        a
  in
  let weight_suffix =
    match transB with
    | [] -> ')'::[]
    | a::s0 ->
      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
        (fun b b0 b1 b2 b3 b4 b5 b6 ->
        if b
        then ')'::[]
        else if b0
             then ')'::[]
             else if b1
                  then ')'::[]
                  else if b2
                       then ')'::[]
                       else if b3
                            then if b4
                                 then if b5
                                      then ')'::[]
                                      else if b6
                                           then ')'::[]
                                           else (match s0 with
                                                 | [] -> ')'::[]
                                                 | a0::s1 ->
                                                   (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                     (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                     if b7
                                                     then ')'::[]
                                                     else if b8
                                                          then if b9
                                                               then if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    ')'::[]
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    ')'::[]
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    ')'::[]
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    ')'::[]
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    ')'::[]
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    ')'::[]
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    ')'::[]
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    ')'::[]
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    ')'::[]
                                                                    else 
                                                                    if b22
                                                                    then 
                                                                    ')'::[]
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    ' '::[]
                                                                    | _::_ ->
                                                                    ')'::[])
                                                                    else 
                                                                    ')'::[]
                                                                    else 
                                                                    ')'::[])
                                                                    a1)
                                                                    else 
                                                                    ')'::[]
                                                                    else 
                                                                    ')'::[]
                                                               else ')'::[]
                                                          else ')'::[])
                                                     a0)
                                 else ')'::[]
                            else ')'::[])
        a
  in
  let bias_prefix =
    match beta with
    | [] ->
      append
        ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
        (append beta ('"'::(')'::(' '::[]))))
    | a::s0 ->
      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
        (fun b b0 b1 b2 b3 b4 b5 b6 ->
        if b
        then if b0
             then append
                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                    (append beta ('"'::(')'::(' '::[]))))
             else if b1
                  then append
                         ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                         (append beta ('"'::(')'::(' '::[]))))
                  else if b2
                       then append
                              ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                              (append beta ('"'::(')'::(' '::[]))))
                       else if b3
                            then if b4
                                 then if b5
                                      then append
                                             ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                             (append beta
                                               ('"'::(')'::(' '::[]))))
                                      else if b6
                                           then append
                                                  ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                  (append beta
                                                    ('"'::(')'::(' '::[]))))
                                           else (match s0 with
                                                 | [] ->
                                                   append
                                                     ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                     (append beta
                                                       ('"'::(')'::(' '::[]))))
                                                 | a0::s1 ->
                                                   (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                     (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                     if b7
                                                     then append
                                                            ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                            (append beta
                                                              ('"'::(')'::(' '::[]))))
                                                     else if b8
                                                          then if b9
                                                               then if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    if b22
                                                                    then 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    (match s2 with
                                                                    | [] -> []
                                                                    | _::_ ->
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[])))))
                                                                    else 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[])))))
                                                                    a1)
                                                                    else 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                                    else 
                                                                    append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                               else append
                                                                    ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                    (append
                                                                    beta
                                                                    ('"'::(')'::(' '::[]))))
                                                          else append
                                                                 ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                                                 (append beta
                                                                   ('"'::(')'::(' '::[])))))
                                                     a0)
                                 else append
                                        ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                        (append beta ('"'::(')'::(' '::[]))))
                            else append
                                   ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
                                   (append beta ('"'::(')'::(' '::[]))))
        else append
               ('('::('s'::('c'::('a'::('l'::('a'::('r'::('_'::('m'::('u'::('l'::('t'::(' '::('('::('r'::('e'::('a'::('l'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::(' '::('"'::[]))))))))))))))))))))))))))))))
               (append beta ('"'::(')'::(' '::[])))))
        a
  in
  let bias_suffix =
    match beta with
    | [] -> ')'::(' '::[])
    | a::s0 ->
      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
        (fun b b0 b1 b2 b3 b4 b5 b6 ->
        if b
        then if b0
             then ')'::(' '::[])
             else if b1
                  then ')'::(' '::[])
                  else if b2
                       then ')'::(' '::[])
                       else if b3
                            then if b4
                                 then if b5
                                      then ')'::(' '::[])
                                      else if b6
                                           then ')'::(' '::[])
                                           else (match s0 with
                                                 | [] -> ')'::(' '::[])
                                                 | a0::s1 ->
                                                   (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                     (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                     if b7
                                                     then ')'::(' '::[])
                                                     else if b8
                                                          then if b9
                                                               then if b10
                                                                    then 
                                                                    if b11
                                                                    then 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    (match s1 with
                                                                    | [] ->
                                                                    ')'::(' '::[])
                                                                    | a1::s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    if b16
                                                                    then 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    if b17
                                                                    then 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    if b19
                                                                    then 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    if b22
                                                                    then 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    (match s2 with
                                                                    | [] ->
                                                                    ' '::[]
                                                                    | _::_ ->
                                                                    ')'::(' '::[]))
                                                                    else 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    ')'::(' '::[]))
                                                                    a1)
                                                                    else 
                                                                    ')'::(' '::[])
                                                                    else 
                                                                    ')'::(' '::[])
                                                               else ')'::(' '::[])
                                                          else ')'::(' '::[]))
                                                     a0)
                                 else ')'::(' '::[])
                            else ')'::(' '::[])
        else ')'::(' '::[]))
        a
  in
  append
    ('D'::('e'::('f'::('i'::('n'::('i'::('t'::('i'::('o'::('n'::(' '::[])))))))))))
    (append (makeName name)
      (append
        (' '::(':'::('='::(' '::('N'::('N'::('L'::('i'::('n'::('e'::('a'::('r'::(' '::[])))))))))))))
        (append weight_prefix
          (append (makeName weight)
            (append weight_suffix
              (append (' '::[])
                (append bias_prefix
                  (append (makeName bias)
                    (append bias_suffix (append (makeName next) ('.'::[])))))))))))
| NNPremodel_ReLu (name, next) ->
  append
    ('D'::('e'::('f'::('i'::('n'::('i'::('t'::('i'::('o'::('n'::(' '::[])))))))))))
    (append (makeName name)
      (append
        (' '::(':'::('='::(' '::('N'::('N'::('R'::('e'::('L'::('U'::(' '::[])))))))))))
        (append (makeName next) ('.'::[]))))

(** val isOutput : nNPremodel -> bool **)

let isOutput = function
| NNPremodel_Output (_, _) -> true
| _ -> false

(** val oneOutput : nNPremodel -> char list * char list **)

let oneOutput = function
| NNPremodel_Output (name, dim) ->
  ((makeName name),
    (append
      ('('::('N'::('N'::('O'::('u'::('t'::('p'::('u'::('t'::(' '::('('::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('d'::('i'::('m'::(':'::('='::[])))))))))))))))))))))))
      (append (stringifyNat dim) (')'::(')'::[])))))
| _ ->
  (('E'::('r'::('r'::('o'::('r'::(':'::(' '::('n'::('o'::('n'::('-'::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('n'::('o'::('d'::('e'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('i'::('n'::(' '::('o'::('n'::('l'::('y'::('-'::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('l'::('i'::('s'::('t'::(','::(' '::('m'::('e'::('a'::('n'::('i'::('n'::('g'::(' '::('i'::('n'::('s'::('t'::('a'::('l'::('l'::('a'::('t'::('i'::('o'::('n'::(' '::('i'::('s'::(' '::('b'::('r'::('o'::('k'::('e'::('n'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    [])

(** val allOutputs : nNPremodel list -> (char list * char list) list **)

let allOutputs nodelist =
  map oneOutput (filter isOutput nodelist)

(** val addOutput : (char list * char list) list -> char list -> char list **)

let rec addOutput outputs nnseq =
  match outputs with
  | [] -> nnseq
  | p :: t3 ->
    let (var_name, definition) = p in
    addOutput t3 (replaceString nnseq var_name definition)

(** val premodel_stringifier : nNPremodel list -> char list **)

let premodel_stringifier l =
  append
    ('('::('*'::('t'::('h'::('i'::('s'::(' '::('f'::('i'::('l'::('e'::(' '::('w'::('a'::('s'::(' '::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('e'::('d'::(' '::('a'::('u'::('t'::('o'::('m'::('a'::('t'::('i'::('c'::('a'::('l'::('l'::('y'::('*'::(')'::('\n'::('F'::('r'::('o'::('m'::(' '::('C'::('o'::('q'::(' '::('R'::('e'::('q'::('u'::('i'::('r'::('e'::(' '::('I'::('m'::('p'::('o'::('r'::('t'::(' '::('S'::('t'::('r'::('i'::('n'::('g'::('s'::('.'::('S'::('t'::('r'::('i'::('n'::('g'::('.'::('\n'::('F'::('r'::('o'::('m'::(' '::('C'::('o'::('q'::(' '::('R'::('e'::('q'::('u'::('i'::('r'::('e'::(' '::('I'::('m'::('p'::('o'::('r'::('t'::(' '::('S'::('t'::('r'::('i'::('n'::('g'::('s'::('.'::('A'::('s'::('c'::('i'::('i'::('.'::('\n'::('\n'::('F'::('r'::('o'::('m'::(' '::('C'::('o'::('q'::(' '::('R'::('e'::('q'::('u'::('i'::('r'::('e'::(' '::('I'::('m'::('p'::('o'::('r'::('t'::(' '::('R'::('e'::('a'::('l'::('s'::('.'::('\n'::('F'::('r'::('o'::('m'::(' '::('C'::('o'::('q'::('u'::('e'::('l'::('i'::('c'::('o'::('t'::(' '::('R'::('e'::('q'::('u'::('i'::('r'::('e'::(' '::('I'::('m'::('p'::('o'::('r'::('t'::(' '::('C'::('o'::('q'::('u'::('e'::('l'::('i'::('c'::('o'::('t'::('.'::('\n'::('F'::('r'::('o'::('m'::(' '::('C'::('o'::('q'::('E'::('2'::('E'::('A'::('I'::(' '::('R'::('e'::('q'::('u'::('i'::('r'::('e'::(' '::('I'::('m'::('p'::('o'::('r'::('t'::(' '::('m'::('a'::('t'::('r'::('i'::('x'::('_'::('e'::('x'::('t'::('e'::('n'::('s'::('i'::('o'::('n'::('s'::(' '::('p'::('i'::('e'::('c'::('e'::('w'::('i'::('s'::('e'::('_'::('a'::('f'::('f'::('i'::('n'::('e'::(' '::('n'::('e'::('u'::('r'::('o'::('n'::('_'::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::('s'::('.'::('\n'::('F'::('r'::('o'::('m'::(' '::('C'::('o'::('q'::('E'::('2'::('E'::('A'::('I'::(' '::('R'::('e'::('q'::('u'::('i'::('r'::('e'::(' '::('I'::('m'::('p'::('o'::('r'::('t'::(' '::('n'::('e'::('u'::('r'::('a'::('l'::('_'::('n'::('e'::('t'::('w'::('o'::('r'::('k'::('s'::('.'::('\n'::('F'::('r'::('o'::('m'::(' '::('C'::('o'::('q'::('E'::('2'::('E'::('A'::('I'::(' '::('R'::('e'::('q'::('u'::('i'::('r'::('e'::(' '::('I'::('m'::('p'::('o'::('r'::('t'::(' '::('s'::('t'::('r'::('i'::('n'::('g'::('_'::('t'::('o'::('_'::('n'::('u'::('m'::('b'::('e'::('r'::('.'::('\n'::('F'::('r'::('o'::('m'::(' '::('C'::('o'::('q'::('E'::('2'::('E'::('A'::('I'::(' '::('R'::('e'::('q'::('u'::('i'::('r'::('e'::(' '::('I'::('m'::('p'::('o'::('r'::('t'::(' '::('t'::('r'::('a'::('n'::('s'::('p'::('o'::('s'::('e'::('_'::('m'::('u'::('l'::('t'::('_'::('m'::('a'::('t'::('r'::('i'::('x'::('.'::('\n'::(' '::(' '::('\n'::('O'::('p'::('e'::('n'::(' '::('S'::('c'::('o'::('p'::('e'::(' '::('n'::('a'::('t'::('_'::('s'::('c'::('o'::('p'::('e'::('.'::('\n'::('\n'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (concat ('\n'::('\n'::[]))
      (map (addOutput (allOutputs l)) (map stringifyNNPremodel l)))

(** val convert_ONNX_to_Coq : char list -> char list **)

let convert_ONNX_to_Coq s0 =
  let conversion =
    error_option_compose
      (error_option_compose
        (error_option_compose (fun raw_onnx ->
          raw_data_converter (list_ascii_of_string raw_onnx)) (fun onnx ->
          filter0 (parser0 (tokenizer onnx)))) (fun token_tree ->
        iR_converter (node_collector token_tree))) premodel_converter
  in
  (match conversion s0 with
   | Success premodel -> premodel_stringifier premodel
   | Error description -> description)

(** val convert : char list -> char list **)

let convert =
  convert_ONNX_to_Coq

(** val input_output_converter :
    char list -> char list -> (char list -> char list) -> unit t1 **)

let input_output_converter input_file output_file f =
  Let ((Obj.magic read_file (LString.s input_file)), (fun read ->
    match Obj.magic read with
    | Some content ->
      Let
        ((Obj.magic write_file (LString.s output_file)
           (LString.s (f (LString.to_string content)))), (fun write ->
        if Obj.magic write
        then log
               (LString.s
                 ('S'::('u'::('c'::('c'::('e'::('s'::('s'::('.'::[])))))))))
        else log
               (LString.s
                 ('U'::('n'::('a'::('b'::('l'::('e'::(' '::('t'::('o'::(' '::('w'::('r'::('i'::('t'::('e'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::('.'::[])))))))))))))))))))))))))))))))
    | None ->
      log
        (LString.s
          ('U'::('n'::('a'::('b'::('l'::('e'::(' '::('t'::('o'::(' '::('r'::('e'::('a'::('d'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::('.'::[])))))))))))))))))))))))))))))

(** val main : LString.t list -> unit t1 **)

let main = function
| [] ->
  log
    (LString.s
      ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('w'::('o'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(':'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::(' '::('n'::('a'::('m'::('e'::(' '::('a'::('n'::('d'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::(' '::('n'::('a'::('m'::('e'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| _ :: l ->
  (match l with
   | [] ->
     log
       (LString.s
         ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('w'::('o'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(':'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::(' '::('n'::('a'::('m'::('e'::(' '::('a'::('n'::('d'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::(' '::('n'::('a'::('m'::('e'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   | input_file_name :: l0 ->
     (match l0 with
      | [] ->
        log
          (LString.s
            ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('w'::('o'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(':'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::(' '::('n'::('a'::('m'::('e'::(' '::('a'::('n'::('d'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::(' '::('n'::('a'::('m'::('e'::('.'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      | output_file_name :: l1 ->
        (match l1 with
         | [] ->
           input_output_converter (LString.to_string input_file_name)
             (LString.to_string output_file_name) convert
         | _ :: _ ->
           log
             (LString.s
               ('E'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('e'::('x'::('a'::('c'::('t'::('l'::('y'::(' '::('t'::('w'::('o'::(' '::('a'::('r'::('g'::('u'::('m'::('e'::('n'::('t'::('s'::(':'::(' '::('i'::('n'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::(' '::('n'::('a'::('m'::('e'::(' '::('a'::('n'::('d'::(' '::('o'::('u'::('t'::('p'::('u'::('t'::(' '::('f'::('i'::('l'::('e'::(' '::('n'::('a'::('m'::('e'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val extract : unit **)

let extract =
  launch0 main
