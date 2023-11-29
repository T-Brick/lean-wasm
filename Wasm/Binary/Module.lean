import Wasm.Syntax.Module
import Wasm.Binary.Instr
import Wasm.Syntax.Instr
open Numbers

namespace Wasm.Binary.Module

open Wasm.Syntax Wasm.Syntax.Module

inductive Section (N : Byte) (B : Type) [Opcode B]
| empty
| data : (size : Unsigned32) → (cont : B) → Section N B

nonrec def Section.toOpcode [Opcode B] : Section N B → ByteSeq
  | .empty          => []
  | .data size cont => N :: toOpcode size ++ toOpcode cont

nonrec def Section.ofOpcode [Opcode B] : Bytecode (Section N B) := do
  let n ← Bytecode.readByte
  if N = n then
    let size : Unsigned32 ← ofOpcode
    let init : Unsigned32 := Unsigned.ofNat (← get).length
    let cont : B ← ofOpcode
    let after : Unsigned32 := Unsigned.ofNat (← get).length
    if size = init - after then
      return .data size cont
    Bytecode.errMsg s!"Tried parsing section {N} with size {size} but got {init - after}"
  Bytecode.errMsg s!"Tried parsing section {N} but got id {n}"

instance [Opcode B] : Opcode (Section N B) :=
  ⟨Section.toOpcode, Section.ofOpcode⟩

def Section.Typ := Section 1 (Vec Typ.Func)


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

def Section.Import := Section 2 (Vec Wasm.Syntax.Module.Import)


def Section.Function := Section 3 (Vec Index.Typ)


nonrec def Table.toOpcode (tt : Table) : ByteSeq := toOpcode tt.type
nonrec def Table.ofOpcode : Bytecode Table :=
  Bytecode.err_log "Parsing table section." do
  return Table.mk (← ofOpcode)
instance : Opcode Table := ⟨Table.toOpcode, Table.ofOpcode⟩

def Section.Table := Section 4 (Vec Wasm.Syntax.Module.Table)


nonrec def Memory.toOpcode (mt : Memory) : ByteSeq := toOpcode mt.type
nonrec def Memory.ofOpcode : Bytecode Memory :=
  Bytecode.err_log "Parsing memory section." do
  return Memory.mk (← ofOpcode)
instance : Opcode Memory := ⟨Memory.toOpcode, Memory.ofOpcode⟩

def Section.Memory := Section 5 (Vec Wasm.Syntax.Module.Memory)


nonrec def Global.toOpcode (gt : Global) : ByteSeq :=
  toOpcode gt.type ++ toOpcode gt.init
nonrec def Global.ofOpcode : Bytecode Global :=
  Bytecode.err_log "Parsing global section." do
  let type ← ofOpcode
  let expr ← ofOpcode
  return ⟨type, expr⟩
instance : Opcode Global := ⟨Global.toOpcode, Global.ofOpcode⟩

def Section.Global := Section 6 (Vec Wasm.Syntax.Module.Global)


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

def Section.Export := Section 7 (Vec Wasm.Syntax.Module.Export)


nonrec def Start.toOpcode (st : Start) : ByteSeq := toOpcode st.func
nonrec def Start.ofOpcode : Bytecode Start :=
  Bytecode.err_log "Parsing start section." do
  return Start.mk (← ofOpcode)
instance : Opcode Start := ⟨Start.toOpcode, Start.ofOpcode⟩

def Section.Start := Section 8 Wasm.Syntax.Module.Start


nonrec def Element.toOpcode (e : Element) : ByteSeq :=
  sorry

private def Element.ref_func (i : Index.Function) : Expr :=
  ( Wasm.Syntax.Instr.reference (.func i) :: [], .wasm_end)

nonrec def Element.Kind.ofOpcode : Bytecode Unit := do
  match ← Bytecode.readByte with
  | 0x00 => return ()
  | _    => Bytecode.errMsg "Non-zero element kind."

nonrec def Element.ofOpcode : Bytecode Element :=
  Bytecode.err_log "Parsing element section." do
  let id : Unsigned32 ← ofOpcode
  if id = 0 then
    let e : Expr ← ofOpcode
    let y ← Vec.ofOpcode
    return ⟨.func, y.map ref_func, .active (Unsigned.ofNat 0) e⟩
  if id = 1 then
    let _ ← Element.Kind.ofOpcode
    let y ← Vec.ofOpcode
    return ⟨.func, y.map ref_func, .passive⟩
  if id = 2 then
    let x ← ofOpcode
    let e : Expr ← ofOpcode
    let _ ← Element.Kind.ofOpcode
    let y ← Vec.ofOpcode
    return ⟨.func, y.map ref_func, .active x e⟩
  if id = 3 then
    let _ ← Element.Kind.ofOpcode
    let y ← Vec.ofOpcode
    return ⟨.func, y.map ref_func, .declarative⟩
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

def Section.Element := Section 9 Wasm.Syntax.Module.Element



def Magic.toOpcode : ByteSeq := [0x00, 0x61, 0x73, 0x6D]
def Magic.ofOpcode : Bytecode Unit := do
  match ← get with
  | 0x00 :: 0x61 :: 0x73 :: 0x6D :: rest => set rest; return ()
  | _ => Bytecode.errMsg "Incorrect magic number!"

def Version.toOpcode : ByteSeq := [0x01, 0x00, 0x00, 0x00]
def Version.ofOpcode : Bytecode Unit := do
  match ← get with
  | 0x01 :: 0x00 :: 0x00 :: 0x00 :: rest => set rest; return ()
  | _ => Bytecode.errMsg "Incorrect version number!"
