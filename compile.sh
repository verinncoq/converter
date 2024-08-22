echo -n "Creating folders..."
mkdir -p target
echo -n "1/2 "
mkdir -p target/internal
echo -e "\b\b\b\b2/2 "

echo -n "Compiling helpers..."
coqc -w none -R ./target/internal CoqE2EAI ./helpers/theorems/theorems.v -o ./target/internal/theorems.vo
echo -n -e "1/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/types/error_option.v -o ./target/internal/error_option.vo
echo -n -e "\b\b\b\b\b2/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/eqb_la.v -o ./target/internal/eqb_la.vo
echo -n -e "\b\b\b\b\b3/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/listStringToString.v -o ./target/internal/listStringToString.vo
echo -n -e "\b\b\b\b\b4/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/string_to_number.v -o ./target/internal/string_to_number.vo
echo -n -e "\b\b\b\b\b5/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/types/string_tree.v -o ./target/internal/string_tree.vo
echo -n -e "\b\b\b\b\b6/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/grab.v -o ./target/internal/grab.vo
echo -n -e "\b\b\b\b\b7/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/count_nodes.v -o ./target/internal/count_nodes.vo
echo -n -e "\b\b\b\b\b8/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/inb.v -o ./target/internal/inb.vo
echo -n -e "\b\b\b\b\b9/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/types/intermediate_representation.v -o ./target/internal/intermediate_representation.vo
echo -n -e "\b\b\b\b\b10/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/convert_matrix.v -o ./target/internal/convert_matrix.vo
echo -n -e "\b\b\b\b\b\b11/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/extract_error.v -o ./target/internal/extract_error.vo
echo -n -e "\b\b\b\b\b\b12/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/list_ascii_helpers.v -o ./target/internal/list_ascii_helpers.vo
echo -n -e "\b\b\b\b\b\b13/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/stringifyNNSequential.v -o ./target/internal/stringifyNNSequential.vo
echo -n -e "\b\b\b\b\b\b14/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/escapeSequenceExtractor.v -o ./target/internal/escapeSequenceExtractor.vo
echo -n -e "\b\b\b\b\b\b15/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/stringifyN.v -o ./target/internal/stringifyN.vo
echo -n -e "\b\b\b\b\b\b16/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/split_string_dot.v -o ./target/internal/split_string_dot.vo
echo -n -e "\b\b\b\b\b\b17/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/bitstrings.v -o ./target/internal/bitstrings.vo
echo -n -e "\b\b\b\b\b\b18/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/IEEE754.v -o ./target/internal/IEEE754.vo
echo -n -e "\b\b\b\b\b\b19/20 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/stateful_map.v -o ./target/internal/stateful_map.vo
echo -e "\b\b\b\b\b\b20/20 "

echo -n "Compiling main parts..."
coqc -w none -R ./target/internal CoqE2EAI ./preprocessing/unpack.v -o ./target/internal/unpack.vo
echo -n "1/10 "
coqc -w none -R ./target/internal CoqE2EAI ./preprocessing/raw_data_converter.v -o ./target/internal/raw_data_converter.vo
echo -n -e "\b\b\b\b\b2/10 "
coqc -w none -R ./target/internal CoqE2EAI ./analysis/tokenizer.v -o ./target/internal/tokenizer.vo
echo -n -e "\b\b\b\b\b3/10 "
coqc -w none -R ./target/internal CoqE2EAI ./analysis/parser.v -o ./target/internal/parser.vo
echo -n -e "\b\b\b\b\b4/10 "
coqc -w none -R ./target/internal CoqE2EAI ./convertIR/whitelist.v -o ./target/internal/whitelist.vo
echo -n -e "\b\b\b\b\b5/10 "
coqc -w none -R ./target/internal CoqE2EAI ./convertIR/filter.v -o ./target/internal/filter.vo
echo -n -e "\b\b\b\b\b6/10 "
coqc -w none -R ./target/internal CoqE2EAI ./convertIR/collect_nodes.v -o ./target/internal/collect_nodes.vo
echo -n -e "\b\b\b\b\b7/10 "
coqc -w none -R ./target/internal CoqE2EAI ./convertIR/convert_to_IR.v -o ./target/internal/convert_to_IR.vo
echo -n -e "\b\b\b\b\b8/10 "
coqc -w none -R ./target/internal CoqE2EAI ./convertOut/convert_to_premodel.v -o ./target/internal/convert_to_premodel.vo
echo -n -e "\b\b\b\b\b9/10 "
coqc -w none -R ./target/internal CoqE2EAI ./main.v -o ./target/internal/main.vo
echo -e "\b\b\b\b\b10/10 "

echo "Building OCaml.."
ocamlbuild converter.native -use-ocamlfind -package io-system


echo -n "Compiling files for execution of output..."
coqc -w none -R ./target/internal CoqE2EAI ./helpers/output_execution/matrix_extensions.v -o ./target/internal/matrix_extensions.vo
echo -n -e "1/6 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/output_execution/piecewise_affine.v -o ./target/internal/piecewise_affine.vo
echo -n -e "\b\b\b\b2/6 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/output_execution/pwaf_operations.v -o ./target/internal/pwaf_operations.vo
echo -n -e "\b\b\b\b3/6 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/output_execution/neuron_functions.v -o ./target/internal/neuron_functions.vo
echo -n -e "\b\b\b\b4/6 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/output_execution/neural_networks.v -o ./target/internal/neural_networks.vo
echo -n -e "\b\b\b\b5/6 "
coqc -w none -R ./target/internal CoqE2EAI ./helpers/functions/transpose_mult_matrix.v -o ./target/internal/transpose_mult_matrix.vo
echo -e "\b\b\b\b6/6 "

echo "Done. You may now try to convert an example network: ./converter.native example_net/cartpole_decoded_onnx cartpole.v"
