import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Text.Ident

namespace Wasm.Text

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

def Context.append (r₁ r₂ : Context) : Context :=
  { types    := r₁.types    ++ r₂.types
  , funcs    := r₁.funcs    ++ r₂.funcs
  , tables   := r₁.tables   ++ r₂.tables
  , mems     := r₁.mems     ++ r₂.mems
  , globals  := r₁.globals  ++ r₂.globals
  , elem     := r₁.elem     ++ r₂.elem
  , data     := r₁.data     ++ r₂.data
  , locals   := r₁.locals   ++ r₂.locals
  , labels   := r₁.labels   ++ r₂.labels
  , typedefs := r₁.typedefs ++ r₂.typedefs
  }

end Ident



-- abbrev Trans := ExceptT (Bytecode.Error) (StateM Ident.Context)

-- instance : Monad Bytecode := show Monad (ExceptT _ _) from inferInstance
