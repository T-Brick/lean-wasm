# WasmLean

A formalisation of the semantics of WebAssembly in Lean.

This is currently intended to be used in the target of a C0 (C subset) compiler
also written in Lean. Hence, efforts here will mostly reflect parts of WASM that
are useful there (i.e. Vector and Float related instructions may lag behind
the rest of the project).

## Project Organisation/Structure

Files are generally organised into a similar layout as defined by the WASM spec:
- [Syntax](Wasm/Syntax/) corresponds to [Structure](https://webassembly.github.io/spec/core/syntax/index.html)
- [Validation](Wasm/Validation/) corresponds to [Validation](https://webassembly.github.io/spec/core/valid/index.html)
- [Dynamics](Wasm/Dynamics/) corresponds to [Execution](https://webassembly.github.io/spec/core/exec/index.html)
- [Binary](Wasm/Binary/) corresponds to [Binary Format](https://webassembly.github.io/spec/core/binary/index.html)
- [Text](Wasm/Text/) corresponds to [Text Format](https://webassembly.github.io/spec/core/text/index.html)

The most notably deviation to this is that the WASM definition of integers is
defined in the [Numbers](https://github.com/T-Brick/Numbers) library.

## Progress/Todo

- [ ] Syntax/Structure
  - [ ] Values
    - [x] Bytes
    - [x] Integers
    - [ ] Float
      - Represented by Lean's float
    - [ ] Vectors
    - [x] Names
  - [x] Types
  - [ ] Instructions
    - [ ] Vectors
    - [x] All other instructions
  - [x] Modules
- [ ] Statics/Validation
  - [x] Types
  - [ ] Instructions
    - [ ] Vectors
    - [x] All other instructions
  - [x] Modules
  - [ ] Type-checker
- [ ] Dynamics/Execution
  - [x] Runtime Structure
  - [ ] Numerics
    - [x] Integer Operations
    - [ ] Floating-point Operations
    - [ ] Conversions
  - [ ] Instructions
    - [ ] Numeric
      - [ ] Floating-point
      - [x] All other numerics
    - [x] Reference
    - [ ] Vector
    - [x] Parametric
    - [x] Variable
    - [x] Table
    - [ ] Memory
    - [ ] Blocks
    - [ ] Function Calls
    - [ ] Expressions
  - [ ] Modules
    - [ ] External Typing
    - [ ] Value Typing
    - [ ] Allocation
    - [ ] Instantiation
    - [ ] Invocation
  - [ ] Intepreter
- [ ] Formats
  - [ ] Binary
    - [ ] Parsing
    - [ ] Printing
    - [ ] Validation
  - [ ] Text
    - [ ] Parsing
    - [x] Printing
    - [ ] Validation
