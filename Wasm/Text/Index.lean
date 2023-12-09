import Wasm.Text.Typ
import Wasm.Text.Ident
import Wasm.Text.Translate
import Wasm.Syntax.Index
import Numbers
open Numbers

namespace Wasm.Text.Module

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

@[inline] def Typ.trans (I : Ident.Context)
    : Typ → Option Wasm.Syntax.Module.Index.Typ
  | .num x  => .some x
  | .name v => (I.types.indexOf? (.some v)).map Unsigned.ofNat

@[inline] def Function.trans (I : Ident.Context)
    : Function → Option Wasm.Syntax.Module.Index.Function
  | .num x  => .some x
  | .name v => (I.types.indexOf? (.some v)).map Unsigned.ofNat

@[inline] def Table.trans (I : Ident.Context)
    : Table → Option Wasm.Syntax.Module.Index.Table
  | .num x  => .some x
  | .name v => (I.types.indexOf? (.some v)).map Unsigned.ofNat

@[inline] def Memory.trans (I : Ident.Context)
    : Table → Option Wasm.Syntax.Module.Index.Memory
  | .num x  => .some x
  | .name v => (I.types.indexOf? (.some v)).map Unsigned.ofNat

@[inline] def Global.trans (I : Ident.Context)
    : Table → Option Wasm.Syntax.Module.Index.Global
  | .num x  => .some x
  | .name v => (I.types.indexOf? (.some v)).map Unsigned.ofNat

@[inline] def Element.trans (I : Ident.Context)
    : Table → Option Wasm.Syntax.Module.Index.Element
  | .num x  => .some x
  | .name v => (I.types.indexOf? (.some v)).map Unsigned.ofNat

@[inline] def Data.trans (I : Ident.Context)
    : Table → Option Wasm.Syntax.Module.Index.Data
  | .num x  => .some x
  | .name v => (I.types.indexOf? (.some v)).map Unsigned.ofNat

@[inline] def Local.trans (I : Ident.Context)
    : Table → Option Wasm.Syntax.Module.Index.Local
  | .num x  => .some x
  | .name v => (I.types.indexOf? (.some v)).map Unsigned.ofNat

@[inline] def Label.trans (I : Ident.Context)
    : Table → Option Wasm.Syntax.Module.Index.Label
  | .num x  => .some x
  | .name v => (I.types.indexOf? (.some v)).map Unsigned.ofNat

instance : ToString Typ       := ⟨Index.toString⟩
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

inductive Typeuse
| type_ind : Index.Typ → Typeuse
| param_res : Index.Typ → List Typ.Param → List Typ.Result → Typeuse
| elab_param_res : List Typ.Param → List Typ.Result → Typeuse

def Typeuse.toString : Typeuse → String
  | .type_ind x => s!"(type {x})"
  | .param_res x params res => s!"(type {x} {params} {res})"
  | .elab_param_res params res => s!"{params} {res}"
instance : ToString Typeuse := ⟨Typeuse.toString⟩
