import Wasm.Util
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value
import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Syntax.Module

namespace Wasm.Dynamics.Instance

structure Export where
  name  : Syntax.Value.Name
  value : Value.Extern

structure Module where
  types       : Vec Syntax.Typ.Func
  funcaddrs   : Vec Address.Function
  tableaddrs  : Vec Address.Table
  memaddrs    : Vec Address.Memory
  globaladdrs : Vec Address.Global
  elemaddrs   : Vec Address.Element
  dataaddrs   : Vec Address.Data
  exports     : Vec Instance.Export

structure Function.Internal where
  type : Syntax.Typ.Func
  module : Instance.Module
  code : Syntax.Module.Function

structure Function.Host where
  type : Syntax.Typ.Func
  hostcode : Unit         -- todo add

inductive Function
| internal : Function.Internal → Function
| host     : Function.Host → Function

structure Table where
  type : Syntax.Typ.Table
  elem : Vec Value.Reference

structure Memory where
  type : Syntax.Typ.Mem
  data : Vec Syntax.Value.Byte

structure Global where
  type  : Syntax.Typ.Global
  value : Value

structure Element where
  type : Syntax.Typ.Ref
  elem : Vec Value.Reference

structure Data where
  data : Vec Syntax.Value.Byte


structure Store where
  funcs   : Vec Function
  tables  : Vec Table
  mems    : Vec Memory
  globals : Vec Global
  elems   : Vec Element
  datas   : Vec Data
