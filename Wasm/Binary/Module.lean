import Wasm.Syntax.Module
import Wasm.Binary.Instr
import Wasm.Syntax.Instr
open Numbers

namespace Wasm.Binary.Module

open Wasm.Syntax Wasm.Syntax.Module

inductive Section (N : Byte) (B : Type) [Opcode B]
| empty
| data : (size : Unsigned32) → (cont : B) → Section N B

def Section.mk [Opcode B] (N : Byte) (b : B) : Section N B :=
  let size := Unsigned.ofNat (toOpcode b).length
  .data size b

def Section.mk_opt [Opcode B] (N : Byte) : Option B → Section N B
  | .none   => .empty
  | .some b => Section.mk N b

def Section.toVec [Opcode B] : Section N (Vec B) → Vec B
  | .empty       => Vec.nil
  | .data _ cont => cont

def Section.toOption [Opcode B] : Section N B → Option B
  | .empty       => .none
  | .data _ cont => .some cont

nonrec def Section.toOpcode [Opcode B] : Section N B → ByteSeq
  | .empty          => []
  | .data size cont => N :: toOpcode size ++ toOpcode cont

nonrec def Section.ofOpcode [Opcode B] : Bytecode (Section N B) := do
  if ¬(← Bytecode.at_end) then
    let n ← Bytecode.peekByte
    if N = n then
      let _ ← Bytecode.readByte -- correct section id
      let size : Unsigned32 ← ofOpcode
      Bytecode.err_log s!"Parsing section id={N} size={size}." do
      let init ← Bytecode.pos
      let cont : B ← ofOpcode
      let h_after ← Bytecode.pos
      let rsize := Unsigned.ofNat (h_after - init)
      if size = rsize then return Section.data size cont else
      Bytecode.errMsg s!"Section {N} expected size {size} got {rsize}."
    else return .empty
  else return .empty

instance [Opcode B] : Opcode (Section N B) :=
  ⟨Section.toOpcode, Section.ofOpcode⟩


structure Section.Custom where
  size : Unsigned32
  name : Value.Name
  data : List Byte

abbrev Section.Custom? := Option Section.Custom

-- since we need to know the size to read custom sections, we won't use the
--   section inductive (rather we embed them together for parsing/output).
nonrec def Section.Custom.toOpcode (custom : Custom) : ByteSeq :=
     Wasm.Binary.toOpcode (0 : Byte)
  ++ Wasm.Binary.toOpcode custom.size
  ++ Wasm.Binary.toOpcode custom.name
  ++ (custom.data.map Wasm.Binary.toOpcode).join

nonrec def Section.Custom.ofOpcode : Bytecode Custom :=
  Bytecode.err_log "Parsing custom section." do
  let N ← Wasm.Binary.ofOpcode
  if N ≠ 0 then Bytecode.errMsg "Custom section id mismatch."

  let size : Unsigned32 ← Wasm.Binary.ofOpcode
  let init ← Bytecode.pos
  let name ← Wasm.Binary.ofOpcode
  let datalen := size.toNat - ((← Bytecode.pos) - init)
  let data ← Bytecode.takeBytes datalen
  return ⟨size, name, data.toList⟩

instance : Opcode Section.Custom :=
  ⟨Section.Custom.toOpcode, Section.Custom.ofOpcode⟩


abbrev Section.Typ := Section 1 (Vec Typ.Func)


nonrec def Import.Description.toOpcode : Import.Description → ByteSeq
  | .func x   => 0x00 :: toOpcode x
  | .table tt => 0x01 :: toOpcode tt
  | .mem mt   => 0x02 :: toOpcode mt
  | .globl gt => 0x03 :: toOpcode gt

nonrec def Import.Description.ofOpcode : Bytecode Import.Description :=
  Bytecode.err_log "Parsing import description." do
  match ← Bytecode.readByte with
  | 0x00 => return Import.Description.func  (← ofOpcode)
  | 0x01 => return Import.Description.table (← ofOpcode)
  | 0x02 => return Import.Description.mem   (← ofOpcode)
  | 0x03 => return Import.Description.globl (← ofOpcode)
  | _ => Bytecode.err

instance : Opcode Import.Description :=
  ⟨Import.Description.toOpcode, Import.Description.ofOpcode⟩

nonrec def Import.toOpcode (imp : Import) : ByteSeq :=
  toOpcode imp.module ++ toOpcode imp.name ++ toOpcode imp.desc

nonrec def Import.ofOpcode : Bytecode Import :=
  Bytecode.err_log "Parsing import section." do
  let mod  ← ofOpcode
  let name ← ofOpcode
  let desc ← ofOpcode
  return ⟨mod, name, desc⟩

instance : Opcode Import := ⟨Import.toOpcode, Import.ofOpcode⟩

abbrev Section.Import := Section 2 (Vec Wasm.Syntax.Module.Import)


abbrev Section.Function := Section 3 (Vec Index.Typ)


nonrec def Table.toOpcode (tt : Table) : ByteSeq := toOpcode tt.type
nonrec def Table.ofOpcode : Bytecode Table :=
  Bytecode.err_log "Parsing table section." do
  return Table.mk (← ofOpcode)
instance : Opcode Table := ⟨Table.toOpcode, Table.ofOpcode⟩

abbrev Section.Table := Section 4 (Vec Wasm.Syntax.Module.Table)


nonrec def Memory.toOpcode (mt : Memory) : ByteSeq := toOpcode mt.type
nonrec def Memory.ofOpcode : Bytecode Memory :=
  Bytecode.err_log "Parsing memory section." do
  return Memory.mk (← ofOpcode)
instance : Opcode Memory := ⟨Memory.toOpcode, Memory.ofOpcode⟩

abbrev Section.Memory := Section 5 (Vec Wasm.Syntax.Module.Memory)


nonrec def Global.toOpcode (gt : Global) : ByteSeq :=
  toOpcode gt.type ++ toOpcode gt.init
nonrec def Global.ofOpcode : Bytecode Global :=
  Bytecode.err_log "Parsing global section." do
  let type ← ofOpcode
  let expr ← ofOpcode
  return ⟨type, expr⟩
instance : Opcode Global := ⟨Global.toOpcode, Global.ofOpcode⟩

abbrev Section.Global := Section 6 (Vec Wasm.Syntax.Module.Global)


nonrec def Export.Description.toOpcode : Export.Description → ByteSeq
  | .func x   => 0x00 :: toOpcode x
  | .table tt => 0x01 :: toOpcode tt
  | .mem mt   => 0x02 :: toOpcode mt
  | .globl gt => 0x03 :: toOpcode gt

nonrec def Export.Description.ofOpcode : Bytecode Export.Description :=
  Bytecode.err_log "Parsing export description." do
  match ← Bytecode.readByte with
  | 0x00 => return Export.Description.func  (← ofOpcode)
  | 0x01 => return Export.Description.table (← ofOpcode)
  | 0x02 => return Export.Description.mem   (← ofOpcode)
  | 0x03 => return Export.Description.globl (← ofOpcode)
  | _    => Bytecode.err
instance : Opcode Export.Description :=
  ⟨Export.Description.toOpcode, Export.Description.ofOpcode⟩

nonrec def Export.toOpcode (ex : Export) : ByteSeq :=
  toOpcode ex.name ++ toOpcode ex.desc
nonrec def Export.ofOpcode : Bytecode Export :=
  Bytecode.err_log "Parsing export section." do
  let name ← ofOpcode
  let desc ← ofOpcode
  return ⟨name, desc⟩
instance : Opcode Export := ⟨Export.toOpcode, Export.ofOpcode⟩

abbrev Section.Export := Section 7 (Vec Wasm.Syntax.Module.Export)


nonrec def Start.toOpcode (st : Start) : ByteSeq := toOpcode st.func
nonrec def Start.ofOpcode : Bytecode Start :=
  Bytecode.err_log "Parsing start section." do
  return Start.mk (← ofOpcode)
instance : Opcode Start := ⟨Start.toOpcode, Start.ofOpcode⟩

abbrev Section.Start := Section 8 Wasm.Syntax.Module.Start



nonrec def Element.Kind.ofOpcode : Bytecode Typ.Ref := do
  match ← Bytecode.readByte with
  | 0x00 => return .func
  | _    => Bytecode.errMsg "Non-zero element kind."

-- todo is this right? should it be more complex like the parsing?
nonrec def Element.toOpcode (e : Element) : ByteSeq :=
  match e.mode with
  | .passive     =>
    toOpcode (5 : Unsigned32) ++ toOpcode e.type ++ toOpcode e.init
  | .declarative =>
    toOpcode (7 : Unsigned32) ++ toOpcode e.type ++ toOpcode e.init
  | .active x y  =>
    toOpcode (6 : Unsigned32)
    ++ toOpcode x
    ++ toOpcode y
    ++ toOpcode e.type
    ++ toOpcode e.init

private def Element.ref_func (i : Index.Function) : Expr :=
  ( Wasm.Syntax.Instr.reference (.func i) :: [], .wasm_end)

nonrec def Element.ofOpcode : Bytecode Element :=
  Bytecode.err_log "Parsing element section." do
  let id : Unsigned32 ← ofOpcode
  if id = 0 then
    let e : Expr ← ofOpcode
    let y ← Vec.ofOpcode
    return ⟨.func, y.map ref_func, .active (Unsigned.ofNat 0) e⟩
  if id = 1 then
    let et ← Element.Kind.ofOpcode
    let y ← Vec.ofOpcode
    return ⟨et, y.map ref_func, .passive⟩
  if id = 2 then
    let x ← ofOpcode
    let e : Expr ← ofOpcode
    let et ← Element.Kind.ofOpcode
    let y ← Vec.ofOpcode
    return ⟨et, y.map ref_func, .active x e⟩
  if id = 3 then
    let et ← Element.Kind.ofOpcode
    let y ← Vec.ofOpcode
    return ⟨et, y.map ref_func, .declarative⟩
  if id = 4 then
    let e : Expr ← ofOpcode
    let el ← Vec.ofOpcode
    return ⟨.func, el, .active (Unsigned.ofNat 0) e⟩
  if id = 5 then
    let et ← ofOpcode
    let el ← Vec.ofOpcode
    return ⟨et, el, .passive⟩
  if id = 6 then
    let x ← ofOpcode
    let e : Expr ← ofOpcode
    let et ← ofOpcode
    let el ← Vec.ofOpcode
    return ⟨et, el, .active x e⟩
  if id = 7 then
    let et ← ofOpcode
    let el ← Vec.ofOpcode
    return ⟨et, el, .declarative⟩
  Bytecode.err

instance : Opcode Element := ⟨Element.toOpcode, Element.ofOpcode⟩

abbrev Section.Element := Section 9 (Vec Wasm.Syntax.Module.Element)


structure Code.Locals where
  n : Unsigned32
  t : Typ.Val
structure Code.Func where
  locals : Vec Typ.Val
  expr   : Expr
structure Code where
  -- size : Unsigned32
  code : Code.Func

def Code.Locals.toVec (locals : Code.Locals) : Vec Typ.Val :=
  let lst := List.ofFn (fun (_ : Fin locals.n.toNat) => locals.t)
  ⟨lst, by simp [List.length_ofFn, Vec.max_length, Unsigned.toNat]⟩

def Code.dataidx (c : Code) : List Index.Data :=
  let (ins, _) := c.code.expr
  ins.filterMap (fun i =>
    match i with
    | .memory (.init x)      => .some x
    | .memory (.data_drop x) => .some x
    | _ => .none
  )

nonrec def Code.Locals.toOpcode (locals : Code.Locals) : ByteSeq :=
  toOpcode locals.n ++ toOpcode locals.t
nonrec def Code.Locals.ofOpcode : Bytecode Code.Locals :=
  Bytecode.err_log "Parsing code locals." do
  let n ← ofOpcode
  let t ← ofOpcode
  return ⟨n, t⟩
instance : Opcode (Code.Locals) := ⟨Code.Locals.toOpcode, Code.Locals.ofOpcode⟩

nonrec def Code.Funcs.toOpcode (funcs : Code.Func) : ByteSeq :=
  toOpcode (funcs.locals.map (Locals.mk 1 ·)) ++ toOpcode funcs.expr
nonrec def Code.Funcs.ofOpcode : Bytecode Code.Func :=
  Bytecode.err_log "Parsing code funcs." do
  let t' ← Vec.ofOpcode
  match Vec.join (t'.map Code.Locals.toVec) with
  | .none => Bytecode.errMsg "Exceeded maximum vector length."
  | .some t =>
    let e ← ofOpcode
    return ⟨t, e⟩
instance : Opcode Code.Func := ⟨Code.Funcs.toOpcode, Code.Funcs.ofOpcode⟩

nonrec def Code.toOpcode (code : Code) : ByteSeq :=
  let fs := toOpcode code.code
  let size : Unsigned32 := Unsigned.ofNat fs.length
  toOpcode size ++ fs

nonrec def Code.ofOpcode : Bytecode Code :=
  Bytecode.err_log "Parsing code section." do
  let size : Unsigned32 ← ofOpcode
  let init ← Bytecode.pos
  let code ← Code.Funcs.ofOpcode
  let h_after ← Bytecode.pos
  let rsize := Unsigned.ofNat (h_after - init)
  if size = rsize then return ⟨code⟩
  Bytecode.errMsg s!"Code section expected size {size} got {rsize}."

instance : Opcode Code := ⟨Code.toOpcode, Code.ofOpcode⟩

nonrec abbrev Section.Code := Section 10 (Vec Code)


nonrec def Data.toOpcode (data : Data) : ByteSeq :=
  match data.mode with
  | .passive => toOpcode (1 : Unsigned32) ++ toOpcode data.init
  | .active (0 : Unsigned32) e =>
    toOpcode (0 : Unsigned32) ++ toOpcode e ++ toOpcode data.init
  | .active x e =>
    toOpcode (2 : Unsigned32) ++ toOpcode x ++ toOpcode e ++ toOpcode data.init

nonrec def Data.ofOpcode : Bytecode Data :=
  Bytecode.err_log "Parsing data section." do
  let m : Unsigned32 ← ofOpcode
  if m = 0 then
    let e ← ofOpcode
    let init ← ofOpcode
    return ⟨init, .active (0 : Unsigned32) e⟩
  if m = 1 then
    let init ← ofOpcode
    return ⟨init, .passive⟩
  if m = 2 then
    let x ← ofOpcode
    let e ← ofOpcode
    let init ← ofOpcode
    return ⟨init, .active x e⟩
  Bytecode.errMsg "Unknown data id"

instance : Opcode Data := ⟨Data.toOpcode, Data.ofOpcode⟩

abbrev Section.Data := Section 11 (Vec Wasm.Syntax.Module.Data)
abbrev Section.Data.Count := Section 12 Unsigned32


def Magic.toOpcode : ByteSeq := [0x00, 0x61, 0x73, 0x6D]
def Magic.ofOpcode : Bytecode Unit := do
  match (← Bytecode.takeBytes 4).toList with
  | 0x00 :: 0x61 :: 0x73 :: 0x6D :: [] => return ()
  | res => Bytecode.errMsg s!"Incorrect magic number (got {res})!"

def Version.toOpcode : ByteSeq := [0x01, 0x00, 0x00, 0x00]
def Version.ofOpcode : Bytecode Unit := do
  match (← Bytecode.takeBytes 4).toList with
  | 0x01 :: 0x00 :: 0x00 :: 0x00 :: [] => return ()
  | res => Bytecode.errMsg s!"Incorrect version number (got {res})!"

nonrec def toOpcode (mod : Module) : ByteSeq :=
  let typeidx := mod.funcs.map (·.type)
  let code    := mod.funcs.map (fun f => Code.mk ⟨f.locals, f.body⟩)
  let m       := Unsigned.ofNat mod.datas.length

  let typesec   : Section.Typ        := Section.mk      1 mod.types
  let importsec : Section.Import     := Section.mk      2 mod.imports
  let funcsec   : Section.Function   := Section.mk      3 typeidx
  let tablesec  : Section.Table      := Section.mk      4 mod.tables
  let memsec    : Section.Memory     := Section.mk      5 mod.mems
  let globalsec : Section.Global     := Section.mk      6 mod.globals
  let exportsec : Section.Export     := Section.mk      7 mod.exports
  let startsec  : Section.Start      := Section.mk_opt  8 mod.start
  let elemsec   : Section.Element    := Section.mk      9 mod.elems
  let codesec   : Section.Code       := Section.mk     10 code
  let datasec   : Section.Data       := Section.mk     11 mod.datas
  let datacsec  : Section.Data.Count := Section.mk     12 m

  (Magic.toOpcode) ++ (Version.toOpcode)
  ++ (toOpcode typesec  )
  ++ (toOpcode importsec)
  ++ (toOpcode funcsec  )
  ++ (toOpcode tablesec )
  ++ (toOpcode memsec   )
  ++ (toOpcode globalsec)
  ++ (toOpcode exportsec)
  ++ (toOpcode startsec )
  ++ (toOpcode elemsec  )
  ++ (toOpcode datacsec )
  ++ (toOpcode codesec  )
  ++ (toOpcode datasec  )

-- todo Custom sections
nonrec def ofOpcode : Bytecode Module :=
  Bytecode.err_log "Parsing WASM module." do
  let () ← Magic.ofOpcode
  let () ← Version.ofOpcode
  let () ← Bytecode.log "Magic + Version valid"

  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let typesec   : Section.Typ        ← Section.ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let importsec : Section.Import     ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let funcsec   : Section.Function   ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let tablesec  : Section.Table      ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let memsec    : Section.Memory     ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let globalsec : Section.Global     ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let exportsec : Section.Export     ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let startsec  : Section.Start      ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let elemsec   : Section.Element    ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let datacsec  : Section.Data.Count ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let codesec   : Section.Code       ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode
  let datasec   : Section.Data       ← ofOpcode
  let _c        : Section.Custom?    ← Bytecode.opt ofOpcode

  let n :=
    match funcsec with
    | .data _ cont => cont.length
    | .empty       => 0
  if n_ge_max : n ≥ Vec.max_length then
    Bytecode.errMsg "Function section exceed max vector len." else
  have n_lt_max : n < Vec.max_length := by simp at n_ge_max; exact n_ge_max

  let n' :=
    match codesec with
    | .data _ cont => cont.length
    | .empty       => 0
  if neq_nn' : n ≠ n' then
    Bytecode.errMsg "Function/Code section length mismatch." else
  have eq_nn' : n = n' := by simp at neq_nn'; exact neq_nn'

  let _ ←
    match datacsec with
    | .data _ m =>
      if m ≠ Unsigned.ofNat datasec.toVec.length then
        Bytecode.errMsg "Data/Datacount section mismatch."
    | .empty =>
      if (codesec.toVec.list.map (Code.dataidx)).join.length ≠ 0 then
        Bytecode.errMsg "Data/Datacount section mismatch."

  let funcs : Vector Module.Function n := Vector.ofFn (fun (i : Fin n) =>
      match fs : funcsec with
      | .data _ typeidx =>
        match cs : codesec with
        | .data _ vcode =>
          let code := vcode.get (cast (by simp [eq_nn', cs]) i)

          ⟨ typeidx.get (cast (by simp [Vec.length, fs]) i)
          , code.code.locals
          , code.code.expr
          ⟩
        | .empty => by
          simp [eq_nn', n', cs] at i
          have := i.isLt
          contradiction
      | .empty => by
        simp [n, fs] at i
        have := i.isLt
        contradiction
    )

  return (
    { types   := typesec.toVec
    , funcs   := ⟨funcs.val, by rw [funcs.prop]; exact n_lt_max⟩
    , tables  := tablesec.toVec
    , mems    := memsec.toVec
    , globals := globalsec.toVec
    , elems   := elemsec.toVec
    , datas   := datasec.toVec
    , start   := startsec.toOption
    , imports := importsec.toVec
    , exports := exportsec.toVec
    }
  )

instance : Opcode Module := ⟨toOpcode, ofOpcode⟩
