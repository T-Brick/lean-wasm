import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Text.Ident

namespace Wasm.Text

namespace Ident

structure Context where
  types     : List (Option Ident)  := []
  funcs     : List (Option Ident)  := []
  tables    : List (Option Ident)  := []
  mems      : List (Option Ident)  := []
  globals   : List (Option Ident)  := []
  elem      : List (Option Ident)  := []
  data      : List (Option Ident)  := []
  locals    : List (Option Ident)  := []
  labels    : List (Option Ident)  := []
  typedefs  : List Syntax.Typ.Func := []
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
instance : Append Context := ⟨Context.append⟩

end Ident

structure Trans.Error where
  log : List String

structure Trans.State where
  I     : Ident.Context
  types : List Syntax.Typ.Func

abbrev Trans := ExceptT (Trans.Error) (StateM Trans.State)
instance : Monad Trans := show Monad (ExceptT _ _) from inferInstance

class OfText (α β : Type) where
  ofText : α → Trans β

export OfText (ofText)
instance [OfText α β] : OfText (id α) β := inferInstanceAs (OfText α β)
instance [OfText α β] : OfText α (id β) := inferInstanceAs (OfText α β)
instance [OfText α β] : OfText (Id α) β := inferInstanceAs (OfText α β)
instance [OfText α β] : OfText α (Id β) := inferInstanceAs (OfText α β)

instance [OfText α β] : OfText (List α) (List β) where
  ofText vs := vs.mapM ofText
instance [OfText α β] : OfText (Vec α) (Vec β) where
  ofText vs := vs.mapM ofText

def Trans.updateI (I' : Ident.Context) : Trans Unit := do
  let s ← get
  set { s with I := I' }

namespace Trans.Error

def err : Trans α := throw ⟨[]⟩
def errMsg : String → Trans α := fun msg => throw (⟨[msg]⟩)
@[inline] def err_log (msg : String) (p : Trans α) : Trans α :=
  fun state =>
    ExceptT.adapt (fun err =>
      {err with log := msg :: err.log}
    ) p state

end Trans.Error

@[inline] def Ident.Context.indexOf
    (f : Ident.Context → List (Option Ident))
    (v : Option Ident)
    (msg : String := "")
    : Trans Unsigned32 := do
  match (f (← get).I).indexOf? v with
  | .some x => return Numbers.Unsigned.ofNat x
  | .none   => Trans.Error.errMsg s!"Error finding {msg} Ident."
