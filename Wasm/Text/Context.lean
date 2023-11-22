
import Wasm.Syntax.Typ

namespace Wasm.Text

@[reducible] def Name := String

def Ident.validChar (c : Char) : Bool :=
  c.isAlphanum || "!#$%'*+-./:<=>?@\\^_`|~".any (· = c)

structure Ident where
  name : String
  name_nonempty : name ≠ ""
  name_valid_chars : name.all Ident.validChar
deriving DecidableEq
instance : ToString Ident := ⟨(s!"${·.name}")⟩
instance : ToString (Option Ident) := ⟨(·.map toString |>.getD "")⟩

namespace Ident
structure Context where
  types     : List (Option Ident)
  funcs     : List (Option Ident)
  tables    : List (Option Ident)
  mems      : List (Option Ident)
  globals   : List (Option Ident)
  elem      : List (Option Ident)
  data      : List (Option Ident)
  locals    : List (Option Ident)
  labels    : List (Option Ident)
  typedefs  : List Syntax.Typ.Func
deriving Inhabited

def Context.Wellformed (I : Context) : Prop :=
  ∀ l₁ l₂,
    l₁ ++ l₂ =
      I.types.filterMap (·) ++ I.funcs.filterMap (·) ++ I.tables.filterMap (·)
      ++ I.mems.filterMap (·) ++ I.globals.filterMap (·) ++ I.elem.filterMap (·)
      ++ I.data.filterMap (·) ++ I.locals.filterMap (·)
      ++ I.labels.filterMap (·)
    → List.Disjoint l₁ l₂

def Context.empty : Context :=
  { types    := []
  , funcs    := []
  , tables   := []
  , mems     := []
  , globals  := []
  , elem     := []
  , data     := []
  , locals   := []
  , labels   := []
  , typedefs := []
  }

theorem Context.Wellformed.empty : Context.Wellformed Context.empty := by
  intro l₁ l₂; simp [Context.empty]; intro l₁_nil l₂_nil; simp [*]
