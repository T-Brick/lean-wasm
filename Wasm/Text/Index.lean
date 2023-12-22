import Wasm.Text.Typ
import Wasm.Text.Ident
import Wasm.Text.Trans
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

instance : OfNat Index n := ⟨.num (Unsigned.ofNat n)⟩
instance : Coe Unsigned32 Index := ⟨.num⟩
instance : Coe Ident      Index := ⟨.name⟩

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

instance : OfNat Typ      n := ⟨.num (Unsigned.ofNat n)⟩
instance : OfNat Function n := ⟨.num (Unsigned.ofNat n)⟩
instance : OfNat Table    n := ⟨.num (Unsigned.ofNat n)⟩
instance : OfNat Memory   n := ⟨.num (Unsigned.ofNat n)⟩
instance : OfNat Global   n := ⟨.num (Unsigned.ofNat n)⟩
instance : OfNat Element  n := ⟨.num (Unsigned.ofNat n)⟩
instance : OfNat Data     n := ⟨.num (Unsigned.ofNat n)⟩
instance : OfNat Local    n := ⟨.num (Unsigned.ofNat n)⟩
instance : OfNat Label    n := ⟨.num (Unsigned.ofNat n)⟩

instance : Coe Ident Typ      := ⟨.name⟩
instance : Coe Ident Function := ⟨.name⟩
instance : Coe Ident Table    := ⟨.name⟩
instance : Coe Ident Memory   := ⟨.name⟩
instance : Coe Ident Global   := ⟨.name⟩
instance : Coe Ident Element  := ⟨.name⟩
instance : Coe Ident Data     := ⟨.name⟩
instance : Coe Ident Local    := ⟨.name⟩
instance : Coe Ident Label    := ⟨.name⟩

open Ident.Context

@[inline] def Typ.trans : Typ → Trans Wasm.Syntax.Module.Index.Typ
  | .num x  => return x
  | .name v => indexOf types (.some v) (msg := "Types")
instance : OfText Typ Wasm.Syntax.Module.Index.Typ := ⟨Typ.trans⟩

@[inline] def Function.trans : Function → Trans Syntax.Module.Index.Function
  | .num x  => return x
  | .name v => indexOf funcs (.some v) (msg := "Functions")
instance : OfText Function Syntax.Module.Index.Function := ⟨Function.trans⟩

@[inline] def Table.trans : Table → Trans Wasm.Syntax.Module.Index.Table
  | .num x  => return x
  | .name v => indexOf tables (.some v) (msg := "Tables")
instance : OfText Table Syntax.Module.Index.Table := ⟨Table.trans⟩

@[inline] def Memory.trans : Memory → Trans Wasm.Syntax.Module.Index.Memory
  | .num x  => return x
  | .name v => indexOf mems (.some v) (msg := "Memories")
instance : OfText Memory Syntax.Module.Index.Memory := ⟨Memory.trans⟩

@[inline] def Global.trans : Global → Trans Wasm.Syntax.Module.Index.Global
  | .num x  => return x
  | .name v => indexOf globals (.some v) (msg := "Globals")
instance : OfText Global Syntax.Module.Index.Global := ⟨Global.trans⟩

@[inline] def Element.trans : Element → Trans Wasm.Syntax.Module.Index.Element
  | .num x  => return x
  | .name v => indexOf elem (.some v) (msg := "Elements")
instance : OfText Element Syntax.Module.Index.Element := ⟨Element.trans⟩

@[inline] def Data.trans : Data → Trans Wasm.Syntax.Module.Index.Data
  | .num x  => return x
  | .name v => indexOf data (.some v) (msg := "Data")
instance : OfText Data Syntax.Module.Index.Data := ⟨Data.trans⟩

@[inline] def Local.trans : Local → Trans Wasm.Syntax.Module.Index.Local
  | .num x  => return x
  | .name v => indexOf locals (.some v) (msg := "Locals")
instance : OfText Local Syntax.Module.Index.Local := ⟨Local.trans⟩

@[inline] def Label.trans : Label → Trans Wasm.Syntax.Module.Index.Label
  | .num x  => return x
  | .name v => indexOf labels (.some v) (msg := "Labels")
instance : OfText Label Syntax.Module.Index.Label := ⟨Label.trans⟩

end Index

inductive Typeuse
| type_ind : Index.Typ → Typeuse
| param_res : Index.Typ → List Typ.Param → List Typ.Result → Typeuse
| elab_param_res : List Typ.Param → List Typ.Result → Typeuse

-- alters the state, if it needs to be restored it should be saved there
def Typeuse.trans : Typeuse
                  → Trans Wasm.Syntax.Module.Index.Typ
  | .type_ind x           => do
    let s ← get
    let i : Wasm.Syntax.Module.Index.Typ ← ofText x
    match s.I.typedefs.get? (Unsigned.toNat i) with
    | .some ty =>
      let n := ty.args.length
      let locals := ty.args.list.map (fun _ => none)
      Trans.updateI {Ident.Context.empty with locals}
      return i
    | .none    => Trans.Error.errMsg s!"Typeuse could not find typedef[{i}]"
  | .param_res x t₁ t₂    => do
    let s ← get
    let i : Wasm.Syntax.Module.Index.Typ ← ofText x
    match s.I.typedefs.get? (Unsigned.toNat i) with
    | .some ty =>
      if ty.args == t₁ && ty.result == t₂ then
        let locals := t₁.map (·.1)
        -- todo verify well-formed
        Trans.updateI {Ident.Context.empty with locals}
        return i
      else Trans.Error.errMsg <|
        s!"Typeuse given params/results {t₁}/{t₂} does not match {ty}"
    | .none    => Trans.Error.errMsg s!"Typeuse could not find typedef[{i}]"
  | .elab_param_res t₁ t₂ => do
    let s ← get
    let args := ⟨t₁.map (·.2), by sorry⟩
    let res  := ⟨t₂, by sorry⟩
    let func := ⟨args, res⟩
    match s.I.typedefs.indexOf? func with
    | .some i =>
      let locals := t₁.map (·.1)
      Trans.updateI {Ident.Context.empty with locals}
      return Unsigned.ofNat i
    | .none    =>
      let locals := t₁.map (·.1)
      set { s with I := { Ident.Context.empty with locals }
                 , types := s.types ++ [func]
          }
      return Unsigned.ofNat (s.I.typedefs.length)
instance : OfText Typeuse Wasm.Syntax.Module.Index.Typ := ⟨Typeuse.trans⟩

def Typeuse.toString : Typeuse → String
  | .type_ind x => s!"(type {x})"
  | .param_res x params res => s!"(type {x} {params} {res})"
  | .elab_param_res params res => s!"{params} {res}"
instance : ToString Typeuse := ⟨Typeuse.toString⟩
