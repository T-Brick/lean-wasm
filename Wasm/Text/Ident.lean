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

def Ident.mkValid (name : String) : Option Ident :=
  if h₁ : name = ""
  then none
  else if h₂ : name.all Ident.validChar
  then some ⟨name, h₁, h₂⟩
  else none

def Ident.mkValid! (name : String) : Ident :=
  match Ident.mkValid name with
  | .some i => i
  | .none   => ⟨"!(INVALID IDENT)!", sorry ,sorry⟩

def Ident.parse (name : String) : Option Ident :=
  if name.startsWith "$" then Ident.mkValid (name.drop 1) else none

def Ident.parse! (name : String) : Ident :=
  match Ident.parse name with
  | .some id => id
  | .none => ⟨"!(INVALID IDENT)!", sorry ,sorry⟩
