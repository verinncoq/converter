From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Nat.

From CoqE2EAI Require Export intermediate_representation.
From CoqE2EAI Require Export error_option.

Open Scope string_scope.

(*removes elements of type 'None' from l, keeps all elements of type 'Some'*)
Fixpoint filter_some {T: Type}(l: list (option T)) : list T :=
  match l with
  | [] => []
  | h::t => match h with
            | Some e => e::(filter_some t)
            | None => filter_some t
            end
  end.

(*searches l for first IR_elem that has s as name attribute (or in output_names list in case of IR_node).*)
Fixpoint search_node_name (l: list IR_elem)(s: string): option IR_elem :=
  match l with
  | [] => None
  | h::t => match h with
            | IR_input name dim => match s =? name with
                                   | true => Some (IR_input name dim)
                                   | false => search_node_name t s
                                   end
            | IR_output name dim => match s =? name with
                                    | true => Some (IR_output name dim)
                                    | false => search_node_name t s
                                    end
            | IR_node name inputs outputs op => match find (fun x => x =? s) outputs with
                                           | Some output => Some (IR_node name inputs outputs op)
                                           | None => search_node_name t s
                                           end
            | IR_initializer name v => match s =? name with
                                           | true => Some (IR_initializer name v)
                                           | false => search_node_name t s
                                           end
            end
  end.

Open Scope nat_scope.
(*searches lir for elements with names in ls. Returns None if not all names have been found.
  Returns otherwise the list containing the found elements.*)
Definition search_node_name_list (lir: list IR_elem)(ls: list string): option (list IR_elem) :=
  let mapped := map (search_node_name lir) ls in
  let mapped_filtered := filter_some mapped in
  match length mapped =? length mapped_filtered with
  | true => Some mapped_filtered
  | false => None
  end.


Open Scope string_scope.
(*removes an IR_elem specified by name from l. When found, it gets removed only once. When not found, the list remains the same.*)
Fixpoint remove_IR_elem (l: list IR_elem)(name: string): list IR_elem :=
  match l with
  | [] => []
  | h::t => match h with
            | IR_input s _ => match s =? name with
                              | true => t
                              | false => h::(remove_IR_elem t name)
                              end
            | IR_output s _ => match s =? name with
                               | true => t
                               | false => h::(remove_IR_elem t name)
                               end
            | IR_node s _ _ _ => match s =? name with
                                 | true => t
                                 | false => h::(remove_IR_elem t name)
                                 end
            | IR_initializer s _ => match s =? name with
                                    | true => t
                                    | false => h::(remove_IR_elem t name)
                                    end
            end
  end.


Open Scope list_scope.
Definition append_option {T: Type}(a: error_option T)(b: error_option (list T)) : error_option (list T) :=
  match a with
  | Error s => Error s
  | Success la => match b with
                    | Error s => Error s
                    | Success lb => Success (la::lb)
                    end
   end.

Fixpoint connect_extract_error (l: list (error_option IR_connected_elem)) : error_option (list IR_connected_elem) :=
  match l with
  | [] => Success []
  | h::t => append_option h (connect_extract_error t)
  end.


Fixpoint connect_node (l: list IR_elem)(d: nat)(e: IR_elem): error_option IR_connected_elem :=
  match d with
  | O => Error "Error: reached maximum depth while trying to connect nodes. There must be a loop in the network."
  | S n => match e with
           | IR_input s dim => (*inputs are a recursive fixpoint*)
                               Success (IR_connected_input s dim)
           | IR_output s dim => let search_option := search_node_name l s in
                                match search_option with
                                | Some irelem => let rec := (connect_node (remove_IR_elem l s) n irelem) in
                                                 match rec with
                                                 | Error s => Error s
                                                 | Success irconn => Success (IR_connected_output irconn dim)
                                                 end
                                | None => Error "Error: Did not find node specified by some other node. This means that your onnx file is broken."
                                end
           | IR_node s li lo op => let search_option := search_node_name_list l li in
                                 match search_option with
                                 | Some irelemlist => let rec := map (connect_node (remove_IR_elem l s) n) irelemlist in
                                                      let rec_err := connect_extract_error rec in
                                                      match rec_err with
                                                      | Error s => Error s
                                                      | Success irconnlist => Success (IR_connected_node irconnlist op)
                                                      end
                                 | None => Error "Error: Did not find node specified by some other node. This means that your onnx file is broken."
                                 end
           | IR_initializer s v => (*initializers are a recursive fixpoint*)
                                   Success (IR_connected_initializer v)
           end
  end.


Definition connect_nodes (ft: fourtuple IR_elem): error_option (list IR_connected_elem) :=
  let flatten := flatten_fourtuple_without_output ft in
  let outputs := get_output ft in
  let outmap := map (connect_node flatten (length flatten)) outputs in
  connect_extract_error outmap.