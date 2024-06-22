import Wasm.Vec
import Wasm.Syntax
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value
import Wasm.Dynamics.Instance

namespace Wasm.Dynamics.Stack

structure Frame where
  locals : Vec Value
  module : Instance.Module

def expand (f : Frame)
           (typeIdx : Syntax.Module.Index.Typ)
           (h : typeIdx.val < f.module.types.list.length)
           : Syntax.Typ.Func :=
  f.module.types.list.get ⟨typeIdx.val, h⟩
