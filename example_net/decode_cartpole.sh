# This script requires protoc (apt install protobuf-compiler)
# The decoded cartpole network is saved in cartpole_decoded_onnx
protoc --decode=onnx.ModelProto onnx.proto < cartpole.onnx > cartpole_decoded_onnx