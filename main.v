Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From Coq Require Import Strings.Ascii.
Require Import Io.System.All.
Require Import ListString.All.
Require Import Io.All.

Import ListNotations.
Import C.Notations.
Open Scope string_scope.

From CoqE2EAI Require Export raw_data_converter.
From CoqE2EAI Require Export tokenizer.
From CoqE2EAI Require Export parser.
From CoqE2EAI Require Export filter.
From CoqE2EAI Require Export node_collector.
From CoqE2EAI Require Export IR_converter.
From CoqE2EAI Require Export premodel_converter.
From CoqE2EAI Require Export list_ascii_helpers.
From CoqE2EAI Require Export premodel_stringifier.

Theorem same_node_count: 
  forall (t t_filtered: tree) (IR: fourtuple IR_elem) (p: list NNPremodel),
    filter t = Success t_filtered -> 
    IR_converter (node_collector t_filtered) = Success IR ->
    premodel_converter IR = Success p ->
    count_nodes_without_input t = List.length p.
Proof. 
  intros t t_filtered IR p H0 H1 H2.
  apply same_node_count_premodel_converter in H2.
  apply same_node_count_IR_converter in H1.
  apply no_error_implies_same_node_count_without_input in H0.
  rewrite H2. rewrite H1. rewrite H0.
  rewrite same_node_count_node_collector_without_input.
  reflexivity. 
Qed.

Notation "f |> g" := (error_option_compose f g) (at level 85).  

Definition convert_ONNX_to_Coq (s: string) : string :=
  let conversion := 
    ((fun raw_onnx => raw_data_converter (list_ascii_of_string raw_onnx)) |>
    (fun onnx => filter (parser (tokenizer onnx))) |>
    (fun token_tree => IR_converter (node_collector token_tree)) |>
    (fun ir => premodel_converter ir)) in
  match conversion s with
  | Success premodel => premodel_stringifier premodel
  | Error description => description
  end.

(*convertion function applied to the file's content*)
Definition convert (s: string) : string := convert_ONNX_to_Coq s.

(*the input output programm. All IO related functions are applied here
  input: input file name, output file name, convertion function*)
Definition input_output_converter (input_file output_file: string) (f: string -> string) :=
  let! read := System.read_file (LString.s input_file) in
  match read with
  | None => System.log (LString.s "Unable to read input file.")
  | Some content => let! write := System.write_file (LString.s output_file) (LString.s (f (LString.to_string content))) in
                    match write with
                    | false => System.log(LString.s "Unable to write output file.")
                    | true => System.log(LString.s "Success.")
                    end
  end.


(*the main function. Arguments are the programm execution arguments*)
Definition main (argv : list LString.t) : C.t System.effect unit :=
  match argv with
  | [_; input_file_name; output_file_name] =>
    input_output_converter (LString.to_string input_file_name) (LString.to_string output_file_name) convert
  | _ => System.log (LString.s "Expected exactly two arguments: input file name and output file name.")
  end.

Definition extract := Extraction.launch main.
Extraction "converter" extract.
