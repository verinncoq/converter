# A verified converter for neural networks from ONNX to coq

## What's new?

In version 1.1 of the converter, **Coq.io** is used for the in- and output of Coq. However, this usage is still optional and must be activated manually. But it should provide a faster converter, as well as some bug fixes. Currently, it is only available in Linux.

## Requirements

* The Coq Proof Assistant, version 8.14.1, compiled with OCaml 4.12.1
* Coq.io 4.0.0
* Coquelicot Version 3.2.0 

(Coquelicot is only for executing the output, not necessary for the converter. If not installed, errors are thrown during compilation, which can be ignored)

## Build

To compile, run `compile.sh`. You can also manually compile all files with `coqc`.
