import Wasm.Syntax.Typ
import Wasm.Syntax.Value

namespace Wasm.Text

abbrev Name := Wasm.Syntax.Value.Name
instance : ToString Name := ⟨fun name => s!"\"{name.value}\""⟩

def Ident.validChar (c : Char) : Bool :=
  c.isAlphanum || "!#$%'*+-./:<=>?@\\^_`|~".any (· = c)

structure Ident where
  name : String
  name_nonempty : name ≠ ""
  name_valid_chars : name.all Ident.validChar
deriving DecidableEq
instance : ToString Ident := ⟨(s!"${·.name}")⟩
instance : ToString (Option Ident) := ⟨(·.map toString |>.getD "")⟩
