/- WASM Module indices
  https://webassembly.github.io/spec/core/syntax/modules.html#indices
-/

import Wasm.Syntax.Value
import Numbers
open Numbers

namespace Wasm.Syntax.Module.Index

def Typ       := Unsigned32
def Function  := Unsigned32
def Table     := Unsigned32
def Memory    := Unsigned32
def Global    := Unsigned32
def Element   := Unsigned32
def Data      := Unsigned32
def Local     := Unsigned32
def Label     := Unsigned32

instance : DecidableEq Typ      := Unsigned.deq
instance : DecidableEq Function := Unsigned.deq
instance : DecidableEq Table    := Unsigned.deq
instance : DecidableEq Memory   := Unsigned.deq
instance : DecidableEq Global   := Unsigned.deq
instance : DecidableEq Element  := Unsigned.deq
instance : DecidableEq Data     := Unsigned.deq
instance : DecidableEq Local    := Unsigned.deq
instance : DecidableEq Label    := Unsigned.deq

instance : ToString Typ      := ⟨Unsigned.toString⟩
instance : ToString Function := ⟨Unsigned.toString⟩
instance : ToString Table    := ⟨Unsigned.toString⟩
instance : ToString Memory   := ⟨Unsigned.toString⟩
instance : ToString Global   := ⟨Unsigned.toString⟩
instance : ToString Element  := ⟨Unsigned.toString⟩
instance : ToString Data     := ⟨Unsigned.toString⟩
instance : ToString Local    := ⟨Unsigned.toString⟩
instance : ToString Label    := ⟨Unsigned.toString⟩
