/- Encoding of defintion WASM's module defintion:
    https://webassembly.github.io/spec/core/syntax/instructions.html
-/
import Wasm.Vec
import Wasm.Syntax.Index
import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Syntax.Instr

namespace Wasm.Syntax.Module

structure Function where
  type   : Index.Typ
  locals : Vec Typ.Val
  body   : Expr

structure Table where
  type : Typ.Table

structure Memory where
  type : Typ.Mem

structure Global where
  type : Typ.Global
  init : Expr

inductive Element.Mode
| passive
| active : (table : Index.Table) → (offset : Expr) → Mode
| declarative

structure Element where
  type : Typ.Ref
  init : Vec Expr
  mode : Element.Mode

inductive Data.Mode
| passive
| active : (memory : Index.Memory) → (offset : Expr) → Mode

structure Data where
  init : Vec Value.Byte
  mode : Data.Mode

structure Start where
  func : Index.Function

inductive Export.Description
| func  : Index.Function → Description
| table : Index.Table → Description
| mem   : Index.Memory → Description
| globl : Index.Global → Description

structure Export where
  name : Value.Name
  desc : Export.Description

inductive Import.Description
| func  : Index.Typ → Description
| table : Typ.Table → Description
| mem   : Typ.Mem → Description
| globl : Typ.Global → Description

structure Import where
  module : Value.Name
  name   : Value.Name
  desc   : Import.Description

end Module

structure Module where
  types   : Vec Typ.Func        := Vec.nil
  funcs   : Vec Module.Function := Vec.nil
  tables  : Vec Module.Table    := Vec.nil
  mems    : Vec Module.Memory   := Vec.nil
  globals : Vec Module.Global   := Vec.nil
  elems   : Vec Module.Element  := Vec.nil
  datas   : Vec Module.Data     := Vec.nil
  start   : Option Module.Start := none
  imports : Vec Module.Import   := Vec.nil
  exports : Vec Module.Export   := Vec.nil
