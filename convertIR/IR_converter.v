From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Nat.


From CoqE2EAI Require Export error_option.
From CoqE2EAI Require Export intermediate_representation.
From CoqE2EAI Require Export string_to_number.
From CoqE2EAI Require Export count_nodes.
From CoqE2EAI Require Export extract_error.

(*returns a list containing all the 'Some' elements in the input list*)
Fixpoint filter_some {T: Type}(l: list (option T)) : list T :=
  match l with
  | [] => []
  | h::t => match h with
            | Some e => e::(filter_some t)
            | None => filter_some t
            end
  end.

(*extracts the dimensional information stored in an input node
  t must be a tree with 'input' as root node
  output is an error_option of IR_dim element which can be
    1: IR_dim (in case of success)
    2: String (in case of error, containing the errormessage)
*)
Definition convert_inputToDim (t: tree) : error_option IR_dim :=
  let tensor_type_option := grab (map list_ascii_of_string ["type"; "tensor_type"]) t in
  match tensor_type_option with
  | None => Error "Error: found no 'Tensor' entry in input node. 
                         Please note that 'Sequence', 'Map', 'Optional' and 'SparseTensor' 
                         are either currently not supported or make no sense as a data type 
                         of an input node."
  | Some tensor_type => match grab (map list_ascii_of_string ["shape"; "dim"; "dim_param"]) tensor_type with
                        | Some _ => Error "Error: namespace Shape with attribute 'dim_param' not supported. 
                                                 Supported is only 'dim_value'."
                        | None => let dim := grabAll (map list_ascii_of_string ["shape"]) "dim" tensor_type in
                                  let dim_values_options := map (grab (map list_ascii_of_string ["dim_value"])) dim in
                                  let dim_values := filter_some dim_values_options in
                                  match dim_values with
                                  | [] => Success dim_scalar (*scalar*)
                                  | h::[] => match grab_value [] h with
                                             | None => Error "Error: Specific value of 'dim_value' key doesn't seem to exist (tried to build vector)."
                                             | Some grabbed => match nat_of_string grabbed with
                                                               | None => Error "Error: Specific value of 'dim_value' key doesn't seem to be a nat."
                                                               | Some n => Success (dim_vector n) (*vector*)
                                                               end
                                             end
                                  | h1::h2::[] => match grab_value [] h1 with
                                                  | None => Error "Error: Specific value of 'dim_value' key doesn't seem to exist (tried to build matrix, 1)."
                                                  | Some grabbed1 => match nat_of_string grabbed1 with
                                                                     | None => Error "Error: Specific value of 'dim_value' key doesn't seem to be a nat."
                                                                     | Some n1 => match grab_value [] h2 with
                                                                                  | None => Error "Error: Specific value of 'dim_value' key doesn't seem to exist (tried to build matrix, 2)."
                                                                                  | Some grabbed2 => match nat_of_string grabbed2 with
                                                                                                    | None => Error "Error: Specific value of 'dim_value' key doesn't seem to be a nat."
                                                                                                    | Some n2 => Success (dim_matrix n1 n2) (*matrix*)
                                                                                                    end
                                                                                  end
                                                              end
                                                  end
                                  | h::t => Error "Error: only supported tensor values are scalars, vectors and matrices."
                                  end
                        end
  end.

(*converts an input node into input IR element
  t must be a tree with 'input' as root node
  output is an error_option of IR_elem element which can be
    1: IR_elem (in case of success, always with contructor IR_input)
    2: String (in case of error, containing the errormessage)
*)
Definition convert_input (t: tree) : error_option IR_elem :=
  let name_option := grab_value (map list_ascii_of_string ["name"]) t in
  match name_option with
  | None => Error "Error: found no name entry in input node"
  | Some name => let dim := convert_inputToDim t in
                 match dim with
                 | Error s => Error s
                 | Success irdim => Success (IR_input (string_of_list_ascii name) irdim)
                 end
  end.

(*converts an output node into output IR element
  t must be a tree with 'output' as root node
  output is an error_option of IR_elem element which can be
    1: IR_elem (in case of success, always with contructor IR_output)
    2: String (in case of error, containing the errormessage)
*)
Definition convert_output (t: tree) : error_option IR_elem :=
  let name_option := grab_value (map list_ascii_of_string ["name"]) t in
  match name_option with
  | None => Error"Error: found no name entry in output node"
  | Some name => let dim := convert_inputToDim t in
                 match dim with
                 | Error s => Error s
                 | Success irdim => Success (IR_output (string_of_list_ascii name) irdim)
                 end
  end.

(*converts an attribute into its string, minding if its acutally an element of given type
  t must be a tree with 'attribute' as root node
  output is error_option of a string which can be
    1: String (in case of success, containing the attribute)
    2: String (in case of error, containing the errormessage)
*)
Definition convert_attribute (t: tree) : error_option string :=
  let type_option := grab_value (map list_ascii_of_string ["type"]) t in
  match type_option with
  | None => Error "Error: found no type entry in attribute node"
  | Some type => match string_of_list_ascii type with
                 | "FLOAT" => let name_option := grab_value (map list_ascii_of_string ["name"]) t in
                           match name_option with
                           | None => Error "Error: found no name entry in attribute node"
                           | Some name => let f_option := grab_value (map list_ascii_of_string ["f"]) t in
                                           match f_option with
                                           | None => Error "Error: found no f entry in attribute node"
                                           | Some f => Success (string_of_list_ascii f)
                                           end
                           end
                 | "INT" => let name_option := grab_value (map list_ascii_of_string ["name"]) t in
                           match name_option with
                           | None => Error "Error: found no name entry in attribute node"
                           | Some name => let i_option := grab_value (map list_ascii_of_string ["i"]) t in
                                           match i_option with
                                           | None => Error "Error: found no i entry in attribute node"
                                           | Some i => Success (string_of_list_ascii i)
                                           end
                           end
                 | _ => Error "Error: attributes must be of type 'FLOAT' or 'INT'."
                 end
  end.

Open Scope float_scope.
(*matches attributes of operations to their default value, as described in https://github.com/onnx/onnx/blob/main/docs/Operators.md*)
Definition default_value (op_type attribute_name: string): error_option string :=
  match op_type with
  | """Gemm""" => match attribute_name with
                  | """alpha""" => Success "1"
                  | """beta""" => Success "1"
                  | """transA""" => Success "0"
                  | """transB""" => Success "0"
                  | _ => Error "Error: found no necessary attribute for 'Gemm' and no default value in a 'node'."
                  end
  | _ => Error "Error: found no necessary attribute and no default value in a 'node'."
  end.

Open Scope string_scope.
(*searches in l for trees with attribute root and name key in it with value v in it. if its not found a default value is taken (when its not given)*)
Fixpoint search_attribute (l: list tree)(v op_type: string) : error_option string :=
  match l with
  | [] => default_value op_type v
  | h::t => let name_option := grab_value (map list_ascii_of_string ["name"]) h in
            match name_option with
            | None => search_attribute t v op_type
            | Some name => match (string_of_list_ascii name =? v) with
                           | true => convert_attribute h
                           | false => search_attribute t v op_type
                           end
            end
  end.

(*extracts the operation out of a generic node with 'gemm' as 'op_type'
  t must be a tree with 'node' as root node, t must have the field 'op_type' with 'gemm' as its value. This condition won't be checked
  output is an error_option of IR_operation element which can be
    1: IR_operation (in case of success, always with contructor gemm)
    2: String (in case of error, containing the errormessage)
*)
Definition convert_gemm_attributes (t: tree) : error_option IR_operation :=
  let attributes := grabAll [] "attribute" t in
  match search_attribute attributes """alpha""" """Gemm""" with
  | Error s => Error s
  | Success alpha => match search_attribute attributes """beta""" """Gemm""" with
                       | Error s => Error s
                       | Success beta => match search_attribute attributes """transA""" """Gemm""" with
                                           | Error s => Error s
                                           | Success transA => match search_attribute attributes """transB""" """Gemm""" with
                                                                 | Error s => Error s
                                                                 | Success transB => Success (gemm alpha beta transA transB)
                                                                 end
                                           end
                       end
  end.

(*converts a generic node into node IR element
  t must be a tree with 'node' as root node
  output is an error_option of IR_elem element which can be
    1: IR_elem (in case of success, always with contructor IR_node)
    2: String (in case of error, containing the errormessage)
*)
Definition convert_node (t: tree) : error_option IR_elem :=
  let name := grab_value (map list_ascii_of_string ["name"]) t in
  match name with
  | None => Error "Error: found no 'name' in node."
  | Some name => let inputs := grabAll [] "input" t in
                 match inputs with
                 | [] => Error "Error: found no input in node."
                 | _ => let input_list := filter_some (map (grab_value []) inputs) in
                        let outputs := grabAll [] "output" t in
                           match outputs with
                           | [] => Error "Error: found no output in node."
                           | _ => let output_list := filter_some (map (grab_value []) outputs) in
                                  let op_type_option := grab_value (map list_ascii_of_string ["op_type"]) t in
                                  match op_type_option with
                                  | None => Error "Error: found no 'op_type' value."
                                  | Some op_type => match string_of_list_ascii op_type with
                                                    | """Relu""" => Success (IR_node (string_of_list_ascii name) (map string_of_list_ascii input_list) (map string_of_list_ascii output_list) relu)
                                                    | """Gemm""" => let attributes := convert_gemm_attributes t in
                                                                    match attributes with
                                                                    | Error s => Error s
                                                                    | Success operation => Success (IR_node (string_of_list_ascii name) (map string_of_list_ascii input_list) (map string_of_list_ascii output_list) operation)
                                                                    end
                                                    | _ => Error "Error: forbidden 'op_type' value. This should have been removed by the filter.
                                                                  Maybe you are using a broken installation."
                                                    end
                                  end
                           end
                 end
  end.


(*reads all the coverted data produced by raw_data converter module, puts it in a list
  t must be a tree with 'initializer' as root node
  output is a list of strings
*)
Definition extract_data_converted (t: tree) : list string :=
    map (string_of_list_ascii) (
      filter_some (
        map (grab_value []) (
          grabAll [] "data_converted" t))).

(*this list contains all functions to extract data in initializer node
  should be filled up with more functions when expanding the converter towards other data fields*)
Definition data_extraction_list : list (tree -> (list string)) := 
  [extract_data_converted].


Open Scope nat_scope.
(*tries to execute all functions in list l on tree t, 
    returns: 
      some float list of first function that returned exactly expected_length floats
      none if none is found
*)
Fixpoint extract_data (t: tree)(expected_length: nat)(l: (list (tree -> (list string)))) : option (list string) :=
  match l with
  | [] => None
  | h::tail => let call := (h t) in
               match (length call) =? expected_length with
               | true => Some call
               | false => extract_data t expected_length tail
               end
  end.


(*extracts fixed value from initializer node
  t must be a tree with 'initializer' as root node
  if a 'dims' field has a non-float value, it will be ignored
  output is an error_option of IR_fixedValue element which can be
    1: IR_fixedValue (in case of success, containg the defined value in initializer node)
    2: String (in case of error, containing the errormessage)
*)
Definition convert_IR_fixedValue (t: tree) : error_option IR_fixedValue :=
  let dims := filter_some (map nat_of_string (filter_some (map (grab_value []) (grabAll [] "dims" t)))) in
  match dims with
  | [] => (*scalar, it is assumed that a data field must contain exactly 1 data entry*)
         let data := extract_data t 1 data_extraction_list in
         match data with
         | None => Error "Error: Could not convert data in initializer node. Maybe the type is not supported or you forgot to run 'raw_data_converter.py'."
         | Some l => Success (value dim_scalar l)
         end
  | n::[] => (*vector*)
         let data := extract_data t n data_extraction_list in
         match data with
         | None => Error "Error: Could not convert data in initializer node. Maybe the type is not supported or you forgot to run 'raw_data_converter.py'."
         | Some l => Success (value (dim_vector n) l)
         end
  | n::m::[] => (*matrix*)
         let data := extract_data t (n*m) data_extraction_list in
         match data with
         | None => Error "Error: Could not convert data in initializer node. Maybe the type is not supported or you forgot to run 'raw_data_converter.py'."
         | Some l => Success (value (dim_matrix n m) l)
         end
  | _ => Error "Error: found initializer node data of type tensor, which is not a scalar, vector or matrix. Please note that this is not supported."
  end.

(*converts an initializer node into initializer IR element
  t must be a tree with 'initializer' as root node
  the 'data_type' field won't be checked, it is assumed that data_type is 1 (float). This must be changed in case of expansion.
  output is an error_option of IR_elem element which can be
    1: IR_elem (in case of success, always with contructor IR_initializer)
    2: String (in case of error, containing the errormessage)
*)
Definition convert_initializer (t: tree) : error_option IR_elem :=
  let name_option := grab_value (map list_ascii_of_string ["name"]) t in
  match name_option with
  | None => Error "Error: an initializer node does not define a name."
  | Some name => let fixed_value := convert_IR_fixedValue t in
                 match fixed_value with
                 | Error s => Error s
                 | Success v => Success (IR_initializer (string_of_list_ascii name) v)
                 end
  end.

(*
convert to IR module function. converts all nodes in fourtuple into the IR, using helping functions defined above.
*)
Definition IR_converter (t: fourtuple tree) : error_option (fourtuple IR_elem) :=
  let input_list_option := extract_error (map convert_input (get_input t)) in
  match input_list_option with
  | Error s => Error s
  | Success input_list => let output_list_option := extract_error (map convert_output (get_output t)) in
                            match output_list_option with
                            | Error s => Error s
                            | Success output_list => let node_list_option := extract_error (map convert_node (get_nodes t)) in
                                                       match node_list_option with
                                                       | Error s => Error s
                                                       | Success node_list => let initializer_list_option := extract_error (map convert_initializer (get_initializer t)) in
                                                                                match initializer_list_option with
                                                                                | Error s => Error s
                                                                                | Success initializer_list => Success (ft IR_elem (input_list, output_list, node_list, initializer_list))
                                                                                end
                                                       end
                            end
  end.

(*IR_converter PROOF*)

Lemma same_node_count_IR_converter_input: forall (ft: fourtuple tree),
  length (map convert_input (get_input ft)) = length (get_input ft).
Proof. intros. rewrite map_length. reflexivity. Qed.

Lemma same_node_count_IR_converter_output: forall (ft: fourtuple tree),
  length (map convert_output (get_output ft)) = length (get_output ft).
Proof. intros. rewrite map_length. reflexivity. Qed.

Lemma same_node_count_IR_converter_node: forall (ft: fourtuple tree),
  length (map convert_node (get_nodes ft)) = length (get_nodes ft).
Proof. intros. rewrite map_length. reflexivity. Qed.

Lemma same_node_count_IR_converter_initializer: forall (ft: fourtuple tree),
  length (map convert_initializer (get_initializer ft)) = length (get_initializer ft).
Proof. intros. rewrite map_length. reflexivity. Qed.


Definition getValue_fourtupleIR_elem (eo : error_option (fourtuple IR_elem)): fourtuple IR_elem :=
  match eo with
  | Success f => f
  | Error _ => ft IR_elem ([],[],[],[])
  end.

Theorem same_node_count_IR_converter: forall (ft: fourtuple tree) (tuple: fourtuple IR_elem),
  IR_converter ft = Success tuple -> length (flatten_fourtuple_without_input tuple) = length (flatten_fourtuple_without_input ft).
Proof. intros. unfold IR_converter in H. destruct (extract_error (map convert_input (get_input ft))) eqn:INPUT.
      + destruct (extract_error (map convert_output (get_output ft))) eqn:OUTPUT.
        * destruct (extract_error (map convert_node (get_nodes ft))) eqn:NODE.
          -- destruct (extract_error (map convert_initializer (get_initializer ft))) eqn:INITIALIZER.
             ++ inversion H. unfold flatten_fourtuple_without_input. unfold get_output at 1.
                 unfold get_nodes  at 1. unfold get_initializer  at 1. unfold fst. unfold snd. apply len_add. split.
                   ** rewrite <- same_node_count_IR_converter_output. apply extract_error_length in OUTPUT. apply OUTPUT.
                   ** apply len_add. split.
                      --- rewrite <- same_node_count_IR_converter_node. apply extract_error_length in NODE. apply NODE.
                      --- rewrite <- same_node_count_IR_converter_initializer. apply extract_error_length in INITIALIZER. apply INITIALIZER.
             ++ inversion H.
          -- inversion H.
       * inversion H.
    + inversion H.
Qed.