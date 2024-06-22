/- https://webassembly.github.io/spec/core/valid/conventions.html -/
import Wasm.Syntax

namespace Wasm.Validation

structure Context where
  types       : Vec Syntax.Typ.Func
  funcs       : Vec Syntax.Typ.Func
  tables      : Vec Syntax.Typ.Table
  mems        : Vec Syntax.Typ.Mem
  globals     : Vec Syntax.Typ.Global
  elems       : Vec Syntax.Typ.Ref
  datas       : Vec Unit                 -- todo is this right?
  locals      : Vec Syntax.Typ.Val
  labels      : Vec Syntax.Typ.Result
  wasm_return : Option Syntax.Typ.Result
  refs        : Vec Syntax.Module.Index.Function
