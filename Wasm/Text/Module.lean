import Wasm.Text.Index
import Wasm.Text.Typ
import Wasm.Text.Instr
import Wasm.Text.InstrTrans
import Wasm.Syntax.Module

namespace Wasm.Text.Module

structure Typ where
  lbl : Option Ident
  ft : Typ.Func
instance : Coe Syntax.Typ.Func Typ := ⟨(⟨.none, ·⟩)⟩
instance : OfText Typ Syntax.Typ.Func := ⟨(return ← ofText ·.ft)⟩

inductive Import.Description
| func  : Option Ident → Typeuse           → Description
| table : Option Ident → Syntax.Typ.Table  → Description
| mem   : Option Ident → Syntax.Typ.Mem    → Description
| globl : Option Ident → Syntax.Typ.Global → Description
instance : Coe Syntax.Module.Import.Description Import.Description :=
  ⟨ fun | .func  i => .func  .none (.type_ind i)
        | .table t => .table .none t
        | .mem   m => .mem   .none m
        | .globl g => .globl .none g
  ⟩

def Import.Description.trans
    : Import.Description → Trans Syntax.Module.Import.Description
  | .func  _id tu => do
    let s ← get
    let x ← ofText tu
    Trans.updateI s.I
    return .func x
  | .table _id t  => return .table t
  | .mem   _id m  => return .mem   m
  | .globl _id g  => return .globl g
instance : OfText Import.Description Syntax.Module.Import.Description :=
  ⟨Import.Description.trans⟩

structure Import where
  module : Name
  name   : Name
  desc   : Import.Description
instance : Coe (Syntax.Module.Import) Import :=
  ⟨ fun imp => ⟨imp.module, imp.name, imp.desc⟩ ⟩

def Import.trans (imp : Import) : Trans Syntax.Module.Import := do
  return ⟨imp.module, imp.name, ← ofText imp.desc⟩
instance : OfText Import Syntax.Module.Import := ⟨Import.trans⟩


structure Local where
  lbl : Option Ident
  typ : Syntax.Typ.Val
instance : OfText Local Syntax.Typ.Val := ⟨(return ·.typ)⟩

structure Function where
  lbl : Option Ident
  typeuse : Typeuse
  locals : List Local
  body : List Instr
instance : Coe Syntax.Module.Function Function :=
  ⟨ fun f => ⟨ .none
             , .type_ind f.type
             , f.locals.list.map (⟨.none, .⟩)
             , f.body.1
             ⟩
  ⟩

def Function.trans (func : Function) : Trans Syntax.Module.Function := do
  let s ← get
  let x ← ofText func.typeuse
  let locals ← ofText func.locals
  let I'' := s.I ++ (← get).I ++ {locals := func.locals.map (·.1)}
  Trans.updateI I''
  let ins ← ofText func.body
  -- todo: check I'' well-formed
  return ⟨x, ⟨locals, sorry⟩, ins⟩
instance : OfText Function Syntax.Module.Function := ⟨Function.trans⟩


structure Table where
  lbl : Option Ident
  type : Syntax.Typ.Table
instance : Coe Syntax.Module.Table Table := ⟨ fun tab => ⟨.none, tab.type⟩ ⟩
instance : OfText Table Syntax.Module.Table := ⟨(return ⟨·.type⟩)⟩


structure Memory where
  lbl : Option Ident
  type : Syntax.Typ.Mem
instance : Coe Syntax.Module.Memory Memory :=
  ⟨ fun mem => ⟨.none, mem.type⟩ ⟩
instance : OfText Memory Syntax.Module.Memory := ⟨(return ⟨·.type⟩)⟩


structure Global where
  lbl : Option Ident
  type : Syntax.Typ.Global
  init : Expr
instance : Coe Syntax.Module.Global Global :=
  ⟨fun g => ⟨.none, g.type, g.init.1⟩⟩
instance : OfText Global Syntax.Module.Global :=
  ⟨fun g => return ⟨g.type, ← ofText g.init⟩⟩


inductive Export.Description
| func  : Index.Function → Description
| table : Index.Table    → Description
| mem   : Index.Memory   → Description
| globl : Index.Global   → Description
instance : Coe Syntax.Module.Export.Description Export.Description :=
  ⟨ fun | .func  i => .func  i
        | .table t => .table t
        | .mem   m => .mem   m
        | .globl g => .globl g
  ⟩
instance : OfText Export.Description Syntax.Module.Export.Description :=
  ⟨ fun | .func  i => return .func  (← ofText i)
        | .table t => return .table (← ofText t)
        | .mem   m => return .mem   (← ofText m)
        | .globl g => return .globl (← ofText g)
  ⟩

structure Export where
  name : Name
  desc : Export.Description
instance : Coe Syntax.Module.Export Export :=
  ⟨ fun exp => ⟨exp.name, exp.desc⟩ ⟩
instance : OfText Export Syntax.Module.Export :=
  ⟨ fun exp => return ⟨exp.name, ← ofText exp.desc⟩ ⟩


structure Start where
  func : Index.Function
instance : Coe Syntax.Module.Start Start := ⟨(⟨·.func⟩)⟩
instance : OfText Start Syntax.Module.Start := ⟨(return ⟨← ofText ·.func⟩)⟩

inductive Element.Mode
| passive
| active : (table : Index.Table) → (offset : Expr) → Mode
| declarative
instance : Coe Syntax.Module.Element.Mode Element.Mode :=
  ⟨ fun | .passive     => .passive
        | .active t e  => .active t e.1
        | .declarative => .declarative
  ⟩
instance : OfText Element.Mode Syntax.Module.Element.Mode :=
  ⟨ fun | .passive     => return .passive
        | .active t e  => return .active (← ofText t) (← ofText e)
        | .declarative => return .declarative
  ⟩

structure Element where
  lbl  : Option Ident
  type : Syntax.Typ.Ref
  init : Vec Expr
  mode : Element.Mode
instance : Coe Syntax.Module.Element Element :=
  ⟨ fun elem => ⟨ .none, elem.type, elem.init.map (·.1), elem.mode⟩ ⟩
instance : OfText Element Syntax.Module.Element :=
  ⟨ fun elem => return ⟨ elem.type, ← ofText elem.init, ← ofText elem.mode ⟩⟩


inductive Data.Mode
| passive
| active : (memory : Index.Memory) → (offset : Expr) → Mode
instance : Coe (Syntax.Module.Data.Mode) Data.Mode :=
  ⟨ fun | .passive    => .passive
        | .active m e => .active m e.1
  ⟩
instance : OfText Data.Mode Syntax.Module.Data.Mode :=
  ⟨ fun | .passive    => return .passive
        | .active m e => return .active (← ofText m) (← ofText e)
  ⟩

structure Data where
  lbl  : Option Ident
  init : Vec Wasm.Syntax.Value.Byte -- todo maybe change fix?
  mode : Data.Mode
instance : Coe Syntax.Module.Data Data :=
  ⟨ fun data => ⟨.none, data.init, data.mode⟩ ⟩
instance : OfText Data Syntax.Module.Data :=
  ⟨ fun data => return ⟨data.init, ← ofText data.mode⟩ ⟩

end Module

inductive Module.Field
  | types   : Module.Typ → Module.Field
  | funcs   : Module.Function → Module.Field
  | tables  : Module.Table → Module.Field
  | mems    : Module.Memory → Module.Field
  | globals : Module.Global → Module.Field
  | elems   : Module.Element → Module.Field
  | datas   : Module.Data → Module.Field
  | start   : Module.Start → Module.Field
  | imports : Module.Import → Module.Field
  | exports : Module.Export → Module.Field

def Module.Field.trans : Module.Field → Trans Syntax.Module
  | .types t   => return { types   := Vec.single (← ofText t)}
  | .funcs f   => return { funcs   := Vec.single (← ofText f)}
  | .tables t  => return { tables  := Vec.single (← ofText t)}
  | .mems m    => return { mems    := Vec.single (← ofText m)}
  | .globals g => return { globals := Vec.single (← ofText g)}
  | .elems e   => return { elems   := Vec.single (← ofText e)}
  | .datas d   => return { datas   := Vec.single (← ofText d)}
  | .start s   => return { start   := some       (← ofText s)}
  | .imports i => return { imports := Vec.single (← ofText i)}
  | .exports e => return { exports := Vec.single (← ofText e)}
instance : OfText Module.Field Syntax.Module := ⟨Module.Field.trans⟩

/- Initial Identifier Context -/
def Module.Field.idc : Module.Field → Ident.Context
  | .types t   => { types   := [t.lbl]
                  , typedefs := [⟨t.ft.args.map (·.2), t.ft.result⟩]
                  }
  | .funcs f   => { funcs   := [f.lbl] }
  | .tables t  => { tables  := [t.lbl] }
  | .mems m    => { mems    := [m.lbl] }
  | .globals g => { globals := [g.lbl] }
  | .elems e   => { elem    := [e.lbl] }
  | .datas d   => { data    := [d.lbl] }
  | .start _   => {}
  | .imports i =>
    match i.desc with
    | .func  id _tu => { funcs   := [id] }
    | .table id _t  => { tables  := [id] }
    | .mem   id _m  => { mems    := [id] }
    | .globl id _g  => { globals := [id] }
  | .exports _ => {}

structure Module where
  lbl : Option Ident         := .none
  fields : List Module.Field := []

def Module.findAll (mod : Module) (p : Module.Field → Option α) : List α :=
  aux mod.fields
where aux : List Module.Field → List α
  | []      => []
  | f :: fs => if let some r := p f then r :: aux fs else aux fs

def Module.findOne (mod : Module) (p : Module.Field → Option α) : Option α :=
  match mod.findAll p with
  | []     => .none
  | r :: _ => .some r

def Module.types : Module → List Module.Typ :=
  (·.findAll (fun | .types t => .some t | _ => .none))
def Module.funcs : Module → List Module.Function :=
  (·.findAll (fun | .funcs f => .some f | _ => .none))
def Module.tables : Module → List Module.Table :=
  (·.findAll (fun | .tables t => .some t | _ => .none))
def Module.mems : Module → List Module.Memory :=
  (·.findAll (fun | .mems m => .some m | _ => .none))
def Module.globals : Module → List Module.Global :=
  (·.findAll (fun | .globals g => .some g | _ => .none))
def Module.elems : Module → List Module.Element :=
  (·.findAll (fun | .elems e => .some e | _ => .none))
def Module.datas : Module → List Module.Data :=
  (·.findAll (fun | .datas d => .some d | _ => .none))
def Module.start : Module → Option Module.Start :=
  (·.findOne (fun | .start s => .some s | _ => .none))
def Module.imports : Module → List Module.Import :=
  (·.findAll (fun | .imports i => .some i | _ => .none))
def Module.exports : Module → List Module.Export :=
  (·.findAll (fun | .exports e => .some e | _ => .none))

def Module.compose (m₁ m₂ : Syntax.Module) : Trans Syntax.Module := do
  match m₁.start, m₂.start with
  | .some _, .some _ =>
    Trans.Error.errMsg s!"Fields contain multiple start functions!"
  | _, _ =>
    if m₂.imports.length > 0 then (do
        if m₁.funcs.length ≠ 0 then
          Trans.Error.errMsg s!"Imports must preceed definitions of functions"
        if m₁.tables.length ≠ 0 then
          Trans.Error.errMsg s!"Imports must preceed definitions of tables"
        if m₁.mems.length ≠ 0 then
          Trans.Error.errMsg s!"Imports must preceed definitions of memories"
        if m₁.globals.length ≠ 0 then
          Trans.Error.errMsg s!"Imports must preceed definitions of globals"
      )
    return { types   := ⟨m₁.types.list   ++ m₂.types.list  , sorry⟩
             funcs   := ⟨m₁.funcs.list   ++ m₂.funcs.list  , sorry⟩
             tables  := ⟨m₁.tables.list  ++ m₂.tables.list , sorry⟩
             mems    := ⟨m₁.mems.list    ++ m₂.mems.list   , sorry⟩
             globals := ⟨m₁.globals.list ++ m₂.globals.list, sorry⟩
             elems   := ⟨m₁.elems.list   ++ m₂.elems.list  , sorry⟩
             datas   := ⟨m₁.datas.list   ++ m₂.datas.list  , sorry⟩
             start   := if m₁.start.isNone then m₂.start else m₁.start
             imports := ⟨m₁.imports.list ++ m₂.imports.list, sorry⟩
             exports := ⟨m₁.exports.list ++ m₂.exports.list, sorry⟩
           }

instance : Coe Syntax.Module Module :=
  ⟨ fun mod => Module.mk .none
      <| (mod.types.list.map   (Module.Field.types  ))
      ++ (mod.imports.list.map (Module.Field.imports))
      ++ (mod.funcs.list.map   (Module.Field.funcs  ))
      ++ (mod.tables.list.map  (Module.Field.tables ))
      ++ (mod.mems.list.map    (Module.Field.mems   ))
      ++ (mod.globals.list.map (Module.Field.globals))
      ++ (mod.elems.list.map   (Module.Field.elems  ))
      ++ (mod.datas.list.map   (Module.Field.datas  ))
      ++ (mod.exports.list.map (Module.Field.exports))
      ++ (match mod.start with | .some s => [Module.Field.start s] | _ => [])
  ⟩

def Module.trans (m : Module) : Trans Syntax.Module := do
  let I := m.fields.map Module.Field.idc
    |>.foldl Ident.Context.append {}
  -- todo check I well-formed!
  Trans.updateI I
  let m ← m.fields.foldlM (fun m₁ f => do
      let s ← get
      let m₂' ← ofText f
      let m₂ ← Module.compose m₂' {types := ⟨s.types, sorry⟩}
      Trans.updateI s.I
      Trans.mergeTypes
      return ← Module.compose m₁ m₂
    ) {}
  let s ← get
  return { m with types := ⟨m.types.list ++ s.I.typedefs, sorry⟩}
instance : OfText Module Syntax.Module := ⟨Module.trans⟩

namespace Module

nonrec def Typ.toString (ty : Typ) : String :=
  s!"(type {ty.lbl} {toString ty.ft})"
instance : ToString Typ := ⟨Typ.toString⟩

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
  let str := data.init.list.map (fun b =>
      match b.toNat with
      | 0x09 => "\\t"
      | 0x0A => "\\n"
      | 0x0D => "\\r"
      | 0x22 => "\\\""
      | 0x27 => "\\'"
      | 0x5C => "\\\\"
      | c =>
        if c ≥ 0x20 && c < 0x7F
        then Char.ofNat c |>.toString
        else s!"\\u\{{c.toHexNumString}}"
    ) |> String.intercalate ""
  s!"(data {data.lbl} {data.mode} \"{str}\")"
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
