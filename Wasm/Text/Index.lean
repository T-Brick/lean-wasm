import Wasm.Text.Context
import Wasm.Text.Typ
import Wasm.Syntax.Index
import Numbers
open Numbers

namespace Wasm.Text.Module

inductive Index.Valid (get : Ident.Context → Unsigned32 → Option Ident)
  : (I : Ident.Context) → Unsigned32 → Type
where
| num  : (x : Unsigned32) → Index.Valid get I x
| name : (v : Ident) → (get I x = .some v) → Index.Valid get I x

inductive Index
| num  : (x : Unsigned32) → Index
| name : (v : Ident) → Index


nonrec def Index.toString : Index → String
  | .num x  => toString x
  | .name v => toString v
instance : ToString Index := ⟨Index.toString⟩


namespace Index

@[inline] def Typ       := Index
@[inline] def Function  := Index
@[inline] def Table     := Index
@[inline] def Memory    := Index
@[inline] def Global    := Index
@[inline] def Element   := Index
@[inline] def Data      := Index
@[inline] def Local     := Index
@[inline] def Label     := Index

@[inline] def Typ.Valid       := Index.Valid (·.types.get? ·.toNat |>.join)
@[inline] def Function.Valid  := Index.Valid (·.funcs.get? ·.toNat |>.join)
@[inline] def Table.Valid     := Index.Valid (·.tables.get? ·.toNat |>.join)
@[inline] def Memory.Valid    := Index.Valid (·.mems.get? ·.toNat |>.join)
@[inline] def Global.Valid    := Index.Valid (·.globals.get? ·.toNat |>.join)
@[inline] def Element.Valid   := Index.Valid (·.elem.get? ·.toNat |>.join)
@[inline] def Data.Valid      := Index.Valid (·.data.get? ·.toNat |>.join)
@[inline] def Local.Valid     := Index.Valid (·.locals.get? ·.toNat |>.join)
@[inline] def Label.Valid     := Index.Valid (·.labels.get? ·.toNat |>.join)

instance : ToString Typ       :=⟨Index.toString⟩
instance : ToString Function  := ⟨Index.toString⟩
instance : ToString Table     := ⟨Index.toString⟩
instance : ToString Memory    := ⟨Index.toString⟩
instance : ToString Global    := ⟨Index.toString⟩
instance : ToString Element   := ⟨Index.toString⟩
instance : ToString Data      := ⟨Index.toString⟩
instance : ToString Local     := ⟨Index.toString⟩
instance : ToString Label     := ⟨Index.toString⟩

instance : Coe Syntax.Module.Index.Typ      Typ       := ⟨(.num ·)⟩
instance : Coe Syntax.Module.Index.Function Function  := ⟨(.num ·)⟩
instance : Coe Syntax.Module.Index.Table    Table     := ⟨(.num ·)⟩
instance : Coe Syntax.Module.Index.Memory   Memory    := ⟨(.num ·)⟩
instance : Coe Syntax.Module.Index.Global   Global    := ⟨(.num ·)⟩
instance : Coe Syntax.Module.Index.Element  Element   := ⟨(.num ·)⟩
instance : Coe Syntax.Module.Index.Data     Data      := ⟨(.num ·)⟩
instance : Coe Syntax.Module.Index.Local    Local     := ⟨(.num ·)⟩
instance : Coe Syntax.Module.Index.Label    Label     := ⟨(.num ·)⟩

instance : Coe (Vec Syntax.Module.Index.Typ)      (Vec Typ)       := ⟨(·.map (.num ·))⟩
instance : Coe (Vec Syntax.Module.Index.Function) (Vec Function)  := ⟨(·.map (.num ·))⟩
instance : Coe (Vec Syntax.Module.Index.Table)    (Vec Table)     := ⟨(·.map (.num ·))⟩
instance : Coe (Vec Syntax.Module.Index.Memory)   (Vec Memory)    := ⟨(·.map (.num ·))⟩
instance : Coe (Vec Syntax.Module.Index.Global)   (Vec Global)    := ⟨(·.map (.num ·))⟩
instance : Coe (Vec Syntax.Module.Index.Element)  (Vec Element)   := ⟨(·.map (.num ·))⟩
instance : Coe (Vec Syntax.Module.Index.Data)     (Vec Data)      := ⟨(·.map (.num ·))⟩
instance : Coe (Vec Syntax.Module.Index.Local)    (Vec Local)     := ⟨(·.map (.num ·))⟩
instance : Coe (Vec Syntax.Module.Index.Label)    (Vec Label)     := ⟨(·.map (.num ·))⟩

end Index

-- todo add other forms
-- inductive Typeuse : (I : Ident.Context) → Index.Typ I → Ident.Context → Type
-- | no_param_res
    -- : (x : Index.Typ I)
    -- → (I.typedefs.get? (x.toNat (·.types.indexOf ∘ .some)) = .some ⟨args, res⟩)
    -- → Typeuse I x { Ident.Context.empty with locals := args.list.map (fun _ => .none) }
-- | 

-- def Typeuse (I : Ident.Context) := List Typ.Param × List Typ.Result

-- instance : ToString (Typeuse I) := ⟨fun (ps, rs) => s!"{ps} {rs}"⟩
