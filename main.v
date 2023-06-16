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
From CoqE2EAI Require Export collect_nodes.
From CoqE2EAI Require Export convert_to_IR.
From CoqE2EAI Require Export convert_to_premodel.
From CoqE2EAI Require Export list_ascii_helpers.
From CoqE2EAI Require Export stringifyNNSequential.

Theorem same_node_count: forall (s raw_data_converted: list ascii)(t: tree)(IR: fourtuple IR_elem)(p: list NNSequential),
  raw_data_converter s = Success raw_data_converted ->
  filter (parse (tokenize raw_data_converted)) = Success t ->
  convert_to_IR (collect_nodes t) = Success IR ->
  convert_to_premodel IR = Success p ->
  count_nodes_without_input t = List.length p.
Proof. intros.
  apply same_node_count_convert_to_premodel in H2.
  apply same_node_count_convert_to_IR in H1.
  rewrite H2. rewrite H1. rewrite same_node_count_collect_nodes_without_input. reflexivity. Qed.

Definition convert_ONNX_to_Coq (s: string) : string :=
  match raw_data_converter (list_ascii_of_string s) with
  | Error e => e
  | Success raw_data_converted => let filtered := filter (parse (tokenize raw_data_converted)) in
             match filtered with
             | Error s => s
             | Success t => let ir_err := convert_to_IR (collect_nodes t) in
                            match ir_err with
                            | Error s => s
                            | Success ir => let pre := convert_to_premodel ir in
                                            match pre with
                                            | Error s => s
                                            | Success nnseq => stringifyNNSequentialList nnseq
                                            end
                            end
             end
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
