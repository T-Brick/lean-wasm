import Wasm.Text.Context
import Wasm.Text.Index
import Wasm.Text.Typ
import Wasm.Text.Instr

namespace Wasm.Text.Module

inductive Import.Description
| func  : Option Ident → Typeuse           → Description
| table : Option Ident → Syntax.Typ.Table  → Description
| mem   : Option Ident → Syntax.Typ.Mem    → Description
| globl : Option Ident → Syntax.Typ.Global → Description

structure Import where
  module : Name
  name   : Name
  desc   : Import.Description

structure Local where
  lbl : Option Ident
  typ : Syntax.Typ.Val

structure Function where
  lbl : Option Ident
  typeuse : Typeuse
  locals : List Local
  body : List Instr

structure Table where
  lbl : Option Ident
  type : Syntax.Typ.Table

structure Memory where
  lbl : Option Ident
  type : Syntax.Typ.Mem

structure Global where
  lbl : Option Ident
  type : Syntax.Typ.Global
  init : Expr

inductive Export.Description
| func  : Index.Function → Description
| table : Index.Table    → Description
| mem   : Index.Memory   → Description
| globl : Index.Global   → Description

structure Export where
  name : Name
  desc : Export.Description

structure Start where
  func : Index.Function

inductive Element.Mode
| passive
| active : (table : Index.Table) → (offset : Expr) → Mode
| declarative

structure Element where
  lbl  : Option Ident
  type : Syntax.Typ.Ref
  init : Vec Expr
  mode : Element.Mode

inductive Data.Mode
| passive
| active : (memory : Index.Memory) → (offset : Expr) → Mode

structure Data where
  lbl  : Option Ident
  init : Vec String
  mode : Data.Mode

end Module

inductive Module.Field
  | types   : Typ.Func → Module.Field
  | funcs   : Module.Function → Module.Field
  | tables  : Module.Table → Module.Field
  | mems    : Module.Memory → Module.Field
  | globals : Module.Global → Module.Field
  | elems   : Module.Element → Module.Field
  | datas   : Module.Data → Module.Field
  | start   : Module.Start → Module.Field
  | imports : Module.Import → Module.Field
  | exports : Module.Export → Module.Field

structure Module where
  lbl : Option Ident
  fields : List Module.Field


namespace Module

def Import.Description.toString : Import.Description → String
  | .func id ty  => s!"(func {id} {ty})"
  | .table id tt => s!"(table {id} {tt})"
  | .mem id mt   => s!"(memory {id} {mt})"
  | .globl id gt => s!"(global {id} {gt})"
instance : ToString (Import.Description) := ⟨Import.Description.toString⟩

def Import.toString (imp : Import) : String :=
  s!"(import {imp.module} {imp.name} {imp.desc})"
instance : ToString Import := ⟨Import.toString⟩
instance : ToString (List Import) :=
  ⟨String.intercalate "\n" ∘ List.map toString⟩

def Local.toString (locl : Local) : String := s!"(local {locl.lbl} {locl.typ})"
instance : ToString Local := ⟨Local.toString⟩
instance : ToString (List Local) := ⟨String.intercalate " " ∘ List.map toString⟩

def Function.toString (f : Function) : String :=
  let body := Instr.listToString f.body |>.replace "\n" "\n  "
  s!"(func {f.lbl} {f.typeuse} {f.locals}\n  {body})"
instance : ToString Function := ⟨Function.toString⟩
instance : ToString (List Function) :=
  ⟨String.intercalate "\n" ∘ List.map toString⟩

def Table.toString (tab : Table) : String := s!"(table {tab.lbl} {tab.type})"
instance : ToString Table := ⟨Table.toString⟩
instance : ToString (List Table) :=
  ⟨String.intercalate "\n" ∘ List.map toString⟩

def Memory.toString (mem : Memory) : String := s!"(memory {mem.lbl} {mem.type})"
instance : ToString Memory := ⟨Memory.toString⟩
instance : ToString (List Memory) :=
  ⟨String.intercalate "\n" ∘ List.map toString⟩

def Global.toString (globl : Global) : String :=
  s!"(global {globl.lbl} {globl.type} {globl.init})"
instance : ToString Global := ⟨Global.toString⟩
instance : ToString (List Global) :=
  ⟨String.intercalate "\n" ∘ List.map toString⟩

def Export.Description.toString : Export.Description → String
  | .func x  => s!"(func {x})"
  | .table x => s!"(table {x})"
  | .mem x   => s!"(memory {x})"
  | .globl x => s!"(global {x})"
instance : ToString (Export.Description) := ⟨Export.Description.toString⟩

def Export.toString (ex : Export) : String := s!"(export {ex.name} {ex.desc})"
instance : ToString Export := ⟨Export.toString⟩
instance : ToString (List Export) :=
  ⟨String.intercalate "\n" ∘ List.map toString⟩

def Start.toString (m : Start) : String := s!"(start {m.func})"
instance : ToString Start := ⟨Start.toString⟩

def Element.Mode.toString : Element.Mode → String
  | .passive         => s!""
  | .active x offset => s!"{x} (offset {offset})"
  | .declarative     => s!"declare"
instance : ToString Element.Mode := ⟨Element.Mode.toString⟩

def Element.toString (elem : Element) : String :=
  s!"(elem {elem.lbl} {elem.mode} {elem.type} {elem.init})"
instance : ToString Element := ⟨Element.toString⟩
instance : ToString (List Element) :=
  ⟨String.intercalate "\n" ∘ List.map toString⟩

def Data.Mode.toString : Data.Mode → String
  | .passive => ""
  | .active i e => s!"(memory {i}) (offset {e})"
instance : ToString Data.Mode := ⟨Data.Mode.toString⟩

def Data.toString (data : Data) : String :=
  s!"(data {data.lbl} {data.mode} {data.init})"
instance : ToString Data := ⟨Data.toString⟩
instance : ToString (List Data) := ⟨String.intercalate "\n" ∘ List.map toString⟩

end Module

nonrec def Module.Field.toString : Module.Field → String
  | .types ty   => toString ty
  | .funcs fn   => toString fn
  | .tables ta  => toString ta
  | .mems me    => toString me
  | .globals gl => toString gl
  | .elems el   => toString el
  | .datas da   => toString da
  | .start st   => toString st
  | .imports im => toString im
  | .exports ex => toString ex
instance : ToString Module.Field := ⟨Module.Field.toString⟩
instance : ToString (List Module.Field) :=
  ⟨String.intercalate "\n" ∘ List.map toString⟩

def Module.toString (m : Module) : String := s!"(module {m.lbl}\n{m.fields}\n)"
instance : ToString Module := ⟨Module.toString⟩
