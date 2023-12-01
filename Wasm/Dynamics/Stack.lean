import Wasm.Vec
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value
import Wasm.Dynamics.Instance
import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Syntax.Module
import Wasm.Syntax.Index

namespace Wasm.Dynamics.Stack

structure Frame where
  locals : Vec Value
  module : Instance.Module

def expand (f : Frame)
           (typeIdx : Syntax.Module.Index.Typ)
           (h : typeIdx.val < f.module.types.list.length)
           : Syntax.Typ.Func :=
  f.module.types.list.get ⟨typeIdx.val, h⟩
