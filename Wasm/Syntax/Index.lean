/- WASM Module indices
  https://webassembly.github.io/spec/core/syntax/modules.html#indices
-/

import Wasm.Syntax.Value

namespace Wasm.Syntax.Module.Index

@[inline] def Typ       := Value.Unsigned32
@[inline] def Function  := Value.Unsigned32
@[inline] def Table     := Value.Unsigned32
@[inline] def Memory    := Value.Unsigned32
@[inline] def Global    := Value.Unsigned32
@[inline] def Element   := Value.Unsigned32
@[inline] def Data      := Value.Unsigned32
@[inline] def Local     := Value.Unsigned32
@[inline] def Label     := Value.Unsigned32

instance : DecidableEq Typ      := Value.Unsigned.deq
instance : DecidableEq Function := Value.Unsigned.deq
instance : DecidableEq Table    := Value.Unsigned.deq
instance : DecidableEq Memory   := Value.Unsigned.deq
instance : DecidableEq Global   := Value.Unsigned.deq
instance : DecidableEq Element  := Value.Unsigned.deq
instance : DecidableEq Data     := Value.Unsigned.deq
instance : DecidableEq Local    := Value.Unsigned.deq
instance : DecidableEq Label    := Value.Unsigned.deq

instance : ToString Typ      := ⟨Value.Unsigned.toString⟩
instance : ToString Function := ⟨Value.Unsigned.toString⟩
instance : ToString Table    := ⟨Value.Unsigned.toString⟩
instance : ToString Memory   := ⟨Value.Unsigned.toString⟩
instance : ToString Global   := ⟨Value.Unsigned.toString⟩
instance : ToString Element  := ⟨Value.Unsigned.toString⟩
instance : ToString Data     := ⟨Value.Unsigned.toString⟩
instance : ToString Local    := ⟨Value.Unsigned.toString⟩
instance : ToString Label    := ⟨Value.Unsigned.toString⟩
