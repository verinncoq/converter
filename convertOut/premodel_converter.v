From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.

From CoqE2EAI Require Export error_option.
From CoqE2EAI Require Export intermediate_representation.
From CoqE2EAI Require Export string_to_number.
From CoqE2EAI Require Export count_nodes.
From CoqE2EAI Require Export convert_matrix.
From CoqE2EAI Require Export extract_error.


(*converts an initializer IR element into NNPremodel
  output is an error_option of NNPremodel element which can be
    1: NNPremodel (in case of success, always with contructor NNPremodel_initializer_vector or NNPremodel_initializer_matrix)
    2: String (in case of error, containing the errormessage)
*)
Definition IR_initializer__to__NNPremodel_IR__initializers (i: IR_elem) : error_option NNPremodel :=
  match i with
  | IR_initializer s fv => match fv with
                           | value dim _ => match dim with
                                               | dim_scalar => Error ("Found a scalar in "++s++". Weights must be matrices, biasses must be vecotors in this modell.")
                                               | dim_vector n => match IR_fixedValue_vector_to_function fv with
                                                               | Some function => Success (NNPremodel_initializer_vector s n function)
                                                               | None => Error ("Error in converting "++s++" to function.")
                                                               end
                                               | dim_matrix n m => match IR_fixedValue_matrix_to_function fv with
                                                               | Some function => Success (NNPremodel_initializer_matrix s n m function)
                                                               | None => Error ("Error in converting "++s++" to function.")
                                                               end
                                               end
                           end
  | _ => Error "Error: found some non-initializer value in initializer list. This might be an implementation error."
  end.

(*converts a node IR element into NNPremodel
  output is an error_option of NNPremodel element which can be
    1: NNPremodel (in case of success, always with contructor NNPremodel_Linear or NNPremodel_ReLu)
    2: String (in case of error, containing the errormessage)
*)
Definition IR_node__to__NNPremodel_IR (i: IR_elem) : error_option NNPremodel :=
  match i with
  | IR_node s li lo op => match op with
                          | relu => (*in this model, relu must have exactly one input and one output*)
                                    match li, lo with
                                    | [input], [output] => Success (NNPremodel_ReLu input output)
                                    | _, _ => Error "Found a relu node with not exactly one input and one output"
                                    end
                          | gemm alpha beta transA transB => (*in this model, relu must have exactly three inputs and one output*)
                                    match alpha, transA with
                                    | "1", "0" => match li, lo with
                                                      | input::weight::[bias], [output] => Success (NNPremodel_Linear input output weight bias transB beta)
                                                      | _, _ => Error "Found a gemm node with not exactly three inputs and one output"
                                                      end
                                    | _, _ => Error "Attribute alpha of gemm operation must be 1 or None AND
                                                        attribute transA of gemm operation be 0 or None"
                                    end
                          end
  | _ => Error "Error: found some non-node value in node list. This might be an implementation error."
  end.

(*converts an output IR element into NNPremodel
  output is an error_option of NNPremodel element which can be
    1: NNPremodel (in case of success, always with contructor NNPremodel_Output)
    2: String (in case of error, containing the errormessage)
*)
Definition IR_output__to__NNPremodel_IR (i: IR_elem) : error_option NNPremodel :=
  match i with
  | IR_output s dim => match dim with
                       | dim_scalar => Error "The output dim cant be a scalar in this model."
                       | dim_vector n => Success (NNPremodel_Output s n)
                       | dim_matrix n m => match n, m with
                                          | 1, _ => Success (NNPremodel_Output s m)
                                          | _, 1 => Success (NNPremodel_Output s n)
                                          | _, _ => Error "The output dim cant be a matrix in this model."
                                          end
                       end
  | _ => Error "Error: found some non-output value in output list. This might be an implementation error."
  end.

(*
premodel_converter module function. Performs all three functions defined above, applied on the IR_elems in the fourtuple.
Ignores input nodes, puts outputs in a list, when no error occurs. But if, first error is part of errormessage.
*)
Open Scope list_scope.
Definition premodel_converter (ft: fourtuple IR_elem) : error_option (list NNPremodel) :=
  let inits := get_initializer ft in
  let nodes := get_nodes ft in
  let outputs := get_output ft in
  let error_option_inits := extract_error (map IR_initializer__to__NNPremodel_IR__initializers inits) in
  let error_option_nodes := extract_error (map IR_node__to__NNPremodel_IR nodes) in
  let error_option_outputs := extract_error (map IR_output__to__NNPremodel_IR outputs) in
  match error_option_inits with
  | Error s => Error s
  | Success just_success_inits => match error_option_nodes with
                                  | Error s => Error s
                                  | Success just_success_nodes => match error_option_outputs with
                                                                  | Error s => Error s
                                                                  | Success just_success_outputs => Success (just_success_inits ++ (rev just_success_outputs) ++ (rev just_success_nodes))
                                                                  end
                                  end
  end.


(*premodel_converter PROOF*)

Theorem same_node_count_premodel_converter: forall (ft: fourtuple IR_elem) (l: list NNPremodel),
  premodel_converter ft = Success l -> length l = length (flatten_fourtuple_without_input ft).
Proof. intros. unfold flatten_fourtuple_without_input. unfold premodel_converter in H. destruct (extract_error
        (map IR_initializer__to__NNPremodel_IR__initializers
           (get_initializer ft))) eqn:P1.
    - destruct (extract_error (map IR_node__to__NNPremodel_IR (get_nodes ft))) eqn:P2.
       + destruct (extract_error (map IR_output__to__NNPremodel_IR (get_output ft))) eqn:P3.
          * inversion H. apply extract_error_length in P1. apply extract_error_length in P2. apply extract_error_length in P3.
            rewrite map_length in P1. rewrite map_length in P2. rewrite map_length in P3.
            rewrite app_length. rewrite P1. rewrite app_length. rewrite rev_length. rewrite rev_length. rewrite P2. rewrite P3.
            repeat rewrite app_length. rewrite add_comm. repeat rewrite <- app_length. rewrite app_assoc. reflexivity.
          * inversion H.
       + inversion H.
    - inversion H.
Qed.
