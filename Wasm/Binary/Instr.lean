import Wasm.Util
import Wasm.Binary.Opcode
import Wasm.Binary.Typ
import Wasm.Binary.Index
import Wasm.Syntax.Typ
import Wasm.Syntax.Instr
import Numbers
open Numbers

namespace Wasm.Binary.Instr

open Wasm.Syntax Wasm.Syntax.Instr

private abbrev Signed33 := Signed ⟨33, by simp⟩

nonrec def BlockType.toOpcode : BlockType → ByteSeq
  | .value .none     => [0x40]
  | .value (.some t) => toOpcode t
  | .index i         => toOpcode (Signed.ofInt i.toInt : Signed33)

nonrec def BlockType.ofOpcode : Bytecode BlockType :=
  Bytecode.err_log "Parsing block type." do
      (do return BlockType.value (.some (← Typ.Val.ofOpcode)))
  <|> (do let x ← ofOpcode (α := Signed33)
          if x ≥ 0 then return .index (Unsigned.ofInt x.toInt)
          else Bytecode.err)
  <|> match ← Bytecode.readByte with
      | 0x40 => return .value .none
      | _    => Bytecode.err

instance : Opcode BlockType := ⟨BlockType.toOpcode, BlockType.ofOpcode⟩


def Pseudo.toOpcode : Pseudo → Byte
  | .wasm_end  => 0x0B
  | .wasm_else => 0x05

def Pseudo.ofOpcode : Bytecode Pseudo :=
  Bytecode.err_log "Parsing pseudo instruction." do
  match ← Bytecode.readByte with
  | 0x0B => return .wasm_end
  | 0x05 => return .wasm_else
  | _    => Bytecode.err

instance : Opcode Pseudo := ⟨Byte.toSeq ∘ Pseudo.toOpcode, Pseudo.ofOpcode⟩


namespace Numeric
open Numeric

namespace Integer
open Integer

-- i32 and i64 have distinct bytecodes, so we need to offset 64bit instrs
private def Unop.opcodeBitOffset : Byte := 0x12

def Unop.toOpcode32 : Unop → Byte
  | .clz    => 0x67
  | .ctz    => 0x68
  | .popcnt => 0x69
def Unop.toOpcode64 (op : Unop) : Byte :=
  Unop.toOpcode32 op + Unop.opcodeBitOffset

def Unop.ofOpcode32 : Bytecode Unop :=
  Bytecode.err_log "Parsing i32 unop instruction." do
  match ← Bytecode.readByte with
  | 0x67 => return .clz
  | 0x68 => return .ctz
  | 0x69 => return .popcnt
  | _    => Bytecode.err
def Unop.ofOpcode64 : Bytecode Unop :=
  Bytecode.err_replace (fun _ => "Parsing i64 unop instruction.") do
  let _ ← Bytecode.modifyByte (· - Unop.opcodeBitOffset)
  return ← Unop.ofOpcode32


-- i32 and i64 have distinct bytecodes, so we need to offset 64bit instrs
private def Binop.opcodeBitOffset : Byte := 0x12

def Binop.toOpcode32 : Binop → Byte
  | .add    => 0x6A
  | .sub    => 0x6B
  | .mul    => 0x6C
  | .div .s => 0x6D
  | .div .u => 0x6E
  | .rem .s => 0x6F
  | .rem .u => 0x70
  | .and    => 0x71
  | .or     => 0x72
  | .xor    => 0x73
  | .shl    => 0x74
  | .shr .s => 0x75
  | .shr .u => 0x76
  | .rotl   => 0x77
  | .rotr   => 0x78
def Binop.toOpcode64 (op : Binop) : Byte :=
  Binop.toOpcode32 op + Binop.opcodeBitOffset

def Binop.ofOpcode32 : Bytecode Binop :=
  Bytecode.err_log "Parsing i32 binop instruction." do
  match ← Bytecode.readByte with
  | 0x6A => return .add
  | 0x6B => return .sub
  | 0x6C => return .mul
  | 0x6D => return .div .s
  | 0x6E => return .div .u
  | 0x6F => return .rem .s
  | 0x70 => return .rem .u
  | 0x71 => return .and
  | 0x72 => return .or
  | 0x73 => return .xor
  | 0x74 => return .shl
  | 0x75 => return .shr .s
  | 0x76 => return .shr .u
  | 0x77 => return .rotl
  | 0x78 => return .rotr
  | _    => Bytecode.err
def Binop.ofOpcode64 : Bytecode Binop :=
  Bytecode.err_replace (fun _ => "Parsing i64 binop instruction.") do
  let _ ← Bytecode.modifyByte (· - Binop.opcodeBitOffset)
  return ← Binop.ofOpcode32


def Test.toOpcode32 : Test → Byte | .eqz => 0x45
def Test.toOpcode64 : Test → Byte | .eqz => 0x50

def Test.ofOpcode32 : Bytecode Test :=
  Bytecode.err_log "Parsing i32 test instruction." do
  match ← Bytecode.readByte with
  | 0x45 => return .eqz
  | _    => Bytecode.err
def Test.ofOpcode64 : Bytecode Test :=
  Bytecode.err_log "Parsing i64 test instruction." do
  match ← Bytecode.readByte with
  | 0x50 => return .eqz
  | _    => Bytecode.err


-- i32 and i64 have distinct bytecodes, so we need to offset 64bit instrs
private def Relation.opcodeBitOffset : Byte := 0xB

def Relation.toOpcode32 : Relation → Byte
  | .eq    => 0x46
  | .ne    => 0x47
  | .lt .s => 0x48
  | .lt .u => 0x49
  | .gt .s => 0x4A
  | .gt .u => 0x4B
  | .le .s => 0x4C
  | .le .u => 0x4D
  | .ge .s => 0x4E
  | .ge .u => 0x4F
def Relation.toOpcode64 (rel : Relation) : Byte :=
  Relation.toOpcode32 rel + Relation.opcodeBitOffset

def Relation.ofOpcode32 : Bytecode Relation :=
  Bytecode.err_log "Parsing i32 relation instruction." do
  match ← Bytecode.readByte with
  | 0x46 => return .eq
  | 0x47 => return .ne
  | 0x48 => return .lt .s
  | 0x49 => return .lt .u
  | 0x4A => return .gt .s
  | 0x4B => return .gt .u
  | 0x4C => return .le .s
  | 0x4D => return .le .u
  | 0x4E => return .ge .s
  | 0x4F => return .ge .u
  | _    => Bytecode.err
def Relation.ofOpcode64 : Bytecode Relation :=
  Bytecode.err_replace (fun _ => "Parsing i64 binop instruction.") do
  let _ ← Bytecode.modifyByte (· - Relation.opcodeBitOffset)
  return ← Relation.ofOpcode32


nonrec def toOpcode : Integer nn → ByteSeq
  | .const v           =>
    match nn with
    | .double => 0x41 :: toOpcode v
    | .quad   => 0x42 :: toOpcode v
  | .unop u            =>
    match nn with
    | .double => [Unop.toOpcode32 u]
    | .quad   => [Unop.toOpcode64 u]
  | .binop b           =>
    match nn with
    | .double => [Binop.toOpcode32 b]
    | .quad   => [Binop.toOpcode64 b]
  | .test t            =>
    match nn with
    | .double => [Test.toOpcode32 t]
    | .quad   => [Test.toOpcode64 t]
  | .relation r        =>
    match nn with
    | .double => [Relation.toOpcode32 r]
    | .quad   => [Relation.toOpcode64 r]
  | .extend8_s         => match nn with | .double => [0xC0] | .quad => [0xC2]
  | .extend16_s        => match nn with | .double => [0xC1] | .quad => [0xC3]
  | .extend32_s        => [0xC4]
  | .wrap_i64          => [0xA7]
  | .extend_i32 .s     => [0xAC]
  | .extend_i32 .u     => [0xAD]
  | .trunc_f mm .s     =>
    match nn with
    | .double => match mm with | .double => [0xA8] | .quad => [0xAA]
    | .quad   => match mm with | .double => [0xA9] | .quad => [0xAB]
  | .trunc_f mm .u     =>
    match nn with
    | .double => match mm with | .double => [0xAE] | .quad => [0xB0]
    | .quad   => match mm with | .double => [0xAF] | .quad => [0xB1]
  | .trunc_sat_f mm .s => 0xFC ::
    match nn with
    | .double =>
      match mm with
      | .double => toOpcode (0 : Unsigned32)
      | .quad   => toOpcode (2 : Unsigned32)
    | .quad   =>
      match mm with
      | .double => toOpcode (4 : Unsigned32)
      | .quad   => toOpcode (6 : Unsigned32)
  | .trunc_sat_f mm .u => 0xFC ::
    match nn with
    | .double =>
      match mm with
      | .double => toOpcode (1 : Unsigned32)
      | .quad   => toOpcode (3 : Unsigned32)
    | .quad   =>
      match mm with
      | .double => toOpcode (5 : Unsigned32)
      | .quad   => toOpcode (7 : Unsigned32)
  | .reinterpret_f     => match nn with | .double => [0xBC] | .quad => [0xBD]

nonrec def ofOpcode : Bytecode (Integer nn) :=
  Bytecode.err_log s!"Parsing i{nn.toBits} instruction." do
  ( match nn with
    | .double =>
          (do return Integer.unop     (← Unop.ofOpcode32    ))
      <|> (do return Integer.binop    (← Binop.ofOpcode32   ))
      <|> (do return Integer.test     (← Test.ofOpcode32    ))
      <|> (do return Integer.relation (← Relation.ofOpcode32))
      <|> (do match ← Bytecode.readByte with
              | 0xA7 => return .wrap_i64
              | 0xA8 => return .trunc_f .double .s
              | 0xA9 => return .trunc_f .double .u
              | 0xAA => return .trunc_f .quad   .s
              | 0xAB => return .trunc_f .quad   .u
              | 0xBC => return .reinterpret_f
              | 0xC0 => return .extend8_s
              | 0xC1 => return .extend16_s
              | 0xFC => do
                let v ← ofOpcode
                if v = 0 then return trunc_sat_f .double .s
                if v = 1 then return trunc_sat_f .double .u
                if v = 2 then return trunc_sat_f .quad   .s
                if v = 3 then return trunc_sat_f .quad   .u
                Bytecode.err
              | _ => Bytecode.err
          )
    | .quad   =>
          (do return Integer.unop     (← Unop.ofOpcode64    ))
      <|> (do return Integer.binop    (← Binop.ofOpcode64   ))
      <|> (do return Integer.test     (← Test.ofOpcode64    ))
      <|> (do return Integer.relation (← Relation.ofOpcode64))
      <|> (do match ← Bytecode.readByte with
              | 0xAC => return .extend_i32 .s
              | 0xAD => return .extend_i32 .u
              | 0xAE => return .trunc_f .double .s
              | 0xAF => return .trunc_f .double .s
              | 0xB0 => return .trunc_f .quad   .s
              | 0xB1 => return .trunc_f .quad   .s
              | 0xBD => return .reinterpret_f
              | 0xC2 => return .extend8_s
              | 0xC3 => return .extend16_s
              | 0xC4 => return .extend32_s
              | 0xFC =>
                let v ← ofOpcode
                if v = 4 then return trunc_sat_f .double .s
                if v = 5 then return trunc_sat_f .double .u
                if v = 6 then return trunc_sat_f .quad   .s
                if v = 7 then return trunc_sat_f .quad   .u
                Bytecode.err
              | _ => Bytecode.err
          )
  ) <|>
    match ← Bytecode.readByte with
    | 0x41 =>
      match size_eq : nn with
      | .double => do
        let const : (Signed nn.toBits) ← ofOpcode
        return .const (cast (by rw [size_eq]) const.toUnsignedN)
      | .quad   => Bytecode.err
    | 0x42 =>
      match size_eq : nn with
      | .double => Bytecode.err
      | .quad   => do
        let const : Signed nn.toBits ← ofOpcode
        return .const (cast (by rw [size_eq]) const.toUnsignedN)
    | _ => Bytecode.err

instance : Opcode (Integer nn) := ⟨toOpcode, ofOpcode⟩

end Integer


namespace Float
open Float

-- f32 and f64 have distinct bytecodes, so we need to offset 64bit instrs
private def Unop.opcodeBitOffset : Byte := 0xE

def Unop.toOpcode32 : Unop → Byte
  | .abs     => 0x8B
  | .neg     => 0x8C
  | .sqrt    => 0x91
  | .ceil    => 0x8D
  | .floor   => 0x8E
  | .trunc   => 0x8F
  | .nearest => 0x90
def Unop.toOpcode64 (op : Unop) : Byte :=
  Unop.toOpcode32 op + Unop.opcodeBitOffset

def Unop.ofOpcode32 : Bytecode Unop :=
  Bytecode.err_log "Parsing f32 unop instruction." do
  match ← Bytecode.readByte with
  | 0x8B => return .abs
  | 0x8C => return .neg
  | 0x91 => return .sqrt
  | 0x8D => return .ceil
  | 0x8E => return .floor
  | 0x8F => return .trunc
  | 0x90 => return .nearest
  | _    => Bytecode.err
def Unop.ofOpcode64 : Bytecode Unop :=
  Bytecode.err_replace (fun _ => "Parsing f64 unop instruction.") do
  let _ ← Bytecode.modifyByte (· - Unop.opcodeBitOffset)
  return ← Unop.ofOpcode32


-- f32 and f64 have distinct bytecodes, so we need to offset 64bit instrs
private def Binop.opcodeBitOffset : Byte := 0xE

def Binop.toOpcode32 : Binop → Byte
  | .add      => 0x92
  | .sub      => 0x93
  | .mul      => 0x94
  | .div      => 0x95
  | .min      => 0x96
  | .max      => 0x97
  | .copysign => 0x98
def Binop.toOpcode64 (op : Binop) : Byte :=
  Binop.toOpcode32 op + Binop.opcodeBitOffset

def Binop.ofOpcode32 : Bytecode Binop :=
  Bytecode.err_log "Parsing f32 binop instruction." do
  match ← Bytecode.readByte with
  | 0x92 => return .add
  | 0x93 => return .sub
  | 0x94 => return .mul
  | 0x95 => return .div
  | 0x96 => return .min
  | 0x97 => return .max
  | 0x98 => return .copysign
  | _    => Bytecode.err
def Binop.ofOpcode64 : Bytecode Binop :=
  Bytecode.err_replace (fun _ => "Parsing f64 binop instruction.") do
  let _ ← Bytecode.modifyByte (· - Binop.opcodeBitOffset)
  return ← Binop.ofOpcode32


-- f32 and f64 have distinct bytecodes, so we need to offset 64bit instrs
private def Relation.opcodeBitOffset : Byte := 0x6

def Relation.toOpcode32 : Relation → Byte
  | .eq => 0x5B
  | .ne => 0x5C
  | .lt => 0x5D
  | .gt => 0x5E
  | .le => 0x5F
  | .ge => 0x60
def Relation.toOpcode64 (rel : Relation) : Byte :=
  Relation.toOpcode32 rel + Relation.opcodeBitOffset

def Relation.ofOpcode32 : Bytecode Relation :=
  Bytecode.err_log "Parsing f32 relation instruction." do
  match ← Bytecode.readByte with
  | 0x5B => return .eq
  | 0x5C => return .ne
  | 0x5D => return .lt
  | 0x5E => return .gt
  | 0x5F => return .le
  | 0x60 => return .ge
  | _    => Bytecode.err
def Relation.ofOpcode64 : Bytecode Relation :=
  Bytecode.err_replace (fun _ => "Parsing f64 relation instruction.") do
  let _ ← Bytecode.modifyByte (· - Relation.opcodeBitOffset)
  return ← Relation.ofOpcode32

nonrec def toOpcode : Float nn → ByteSeq
  | .const v         =>
    match nn with
    | .double => 0x43 :: toOpcode v
    | .quad   => 0x44 :: toOpcode v
  | .unop u          =>
    match nn with
    | .double => [Unop.toOpcode32 u]
    | .quad   => [Unop.toOpcode64 u]
  | .binop b         =>
    match nn with
    | .double => [Binop.toOpcode32 b]
    | .quad   => [Binop.toOpcode64 b]
  | .relation r      =>
    match nn with
    | .double => [Relation.toOpcode32 r]
    | .quad   => [Relation.toOpcode64 r]
  | .demote_f64      => [0xB6]
  | .promote_f32     => [0xBB]
  | .convert_i mm .s =>
    match nn with
    | .double => match mm with | .double => [0xB2] | .quad => [0xB4]
    | .quad   => match mm with | .double => [0xB7] | .quad => [0xB9]
  | .convert_i mm .u =>
    match nn with
    | .double => match mm with | .double => [0xB3] | .quad => [0xB5]
    | .quad   => match mm with | .double => [0xB8] | .quad => [0xBA]
  | .reinterpret_i   => match nn with | .double => [0xBE] | .quad => [0xBF]

nonrec def ofOpcode : Bytecode (Float nn) :=
  Bytecode.err_log s!"Parsing f{nn.toBits} instruction." do
    ( match nn with
      | .double =>
            (return Float.unop     (← Unop.ofOpcode32    ))
        <|> (return Float.binop    (← Binop.ofOpcode32   ))
        <|> (return Float.relation (← Relation.ofOpcode32))
        <|> (do match ← Bytecode.readByte with
                | 0xB2 => return .convert_i .double .s
                | 0xB3 => return .convert_i .double .u
                | 0xB4 => return .convert_i .quad   .s
                | 0xB5 => return .convert_i .quad   .u
                | 0xB6 => return .demote_f64
                | 0xBE => return .reinterpret_i
                | _    => Bytecode.err
            )
      | .quad   =>
            (do return Float.unop     (← Unop.ofOpcode64    ))
        <|> (do return Float.binop    (← Binop.ofOpcode64   ))
        <|> (do return Float.relation (← Relation.ofOpcode64))
        <|> (do match ← Bytecode.readByte with
                | 0xB7 => return .convert_i .double .s
                | 0xB8 => return .convert_i .double .u
                | 0xB9 => return .convert_i .quad   .s
                | 0xBA => return .convert_i .quad   .u
                | 0xBB => return .promote_f32
                | 0xBF => return .reinterpret_i
                | _    => Bytecode.err
            )
    ) <|> (
      match ← Bytecode.readByte with
      | 0x43 =>
        match _size_eq : nn with
        | .double => do
          let v : Wasm.Syntax.Value.FloatN nn.toBits ← ofOpcode
          return .const v
        | .quad   => Bytecode.err
      | 0x44 =>
        match _size_eq : nn with
        | .double => Bytecode.err
        | .quad   => do
          let v : Wasm.Syntax.Value.FloatN nn.toBits ← ofOpcode
          return .const v
      | _ => Bytecode.err
  )

instance : Opcode (Float nn) := ⟨toOpcode, ofOpcode⟩

end Float

def toOpcode : Numeric nn → ByteSeq
  | .integer i => Integer.toOpcode i
  | .float f   => Float.toOpcode f

def ofOpcode : Bytecode (Numeric nn) :=
  Bytecode.err_log "Parsing numeric instruction." do
      (return Numeric.integer (← Integer.ofOpcode))
  <|> (return Numeric.float   (← Float.ofOpcode  ))

instance : Opcode (Numeric nn) := ⟨toOpcode, ofOpcode⟩

end Numeric

nonrec def Reference.toOpcode : Reference → ByteSeq
  | .null t  => 0xD0 :: toOpcode t
  | .is_null => 0xD1 :: []
  | .func f  => 0xD2 :: toOpcode f

nonrec def Reference.ofOpcode : Bytecode Reference :=
  Bytecode.err_log "Parsing reference instruction." do
  match ← Bytecode.readByte with
  | 0xD0 => return Reference.null (← ofOpcode)
  | 0xD1 => return .is_null
  | 0xD2 => return Reference.func (← ofOpcode)
  | _    => Bytecode.err

instance : Opcode Reference := ⟨Reference.toOpcode, Reference.ofOpcode⟩


nonrec def Local.toOpcode : Local → ByteSeq
  | .get l => 0x20 :: toOpcode l
  | .set l => 0x21 :: toOpcode l
  | .tee l => 0x22 :: toOpcode l

nonrec def Local.ofOpcode : Bytecode Local :=
  Bytecode.err_log "Parsing local instruction." do
  match ← Bytecode.readByte with
  | 0x20 => return Local.get (← ofOpcode)
  | 0x21 => return Local.set (← ofOpcode)
  | 0x22 => return Local.tee (← ofOpcode)
  | _    => Bytecode.err

instance : Opcode Local := ⟨Local.toOpcode, Local.ofOpcode⟩


nonrec def Global.toOpcode : Global → ByteSeq
  | .get l => 0x23 :: toOpcode l
  | .set l => 0x24 :: toOpcode l

nonrec def Global.ofOpcode : Bytecode Global :=
  Bytecode.err_log "Parsing global instruction." do
  match ← Bytecode.readByte with
  | 0x23 => return Global.get (← ofOpcode)
  | 0x24 => return Global.set (← ofOpcode)
  | _    => Bytecode.err

instance : Opcode Global := ⟨Global.toOpcode, Global.ofOpcode⟩


nonrec def Table.toOpcode : Table → ByteSeq
  | .get i    => 0x25 :: toOpcode i
  | .set i    => 0x26 :: toOpcode i
  | .size i   => 0xFC :: toOpcode (16 : Unsigned32) ++ toOpcode i
  | .grow i   => 0xFC :: toOpcode (15 : Unsigned32) ++ toOpcode i
  | .fill i   => 0xFC :: toOpcode (17 : Unsigned32) ++ toOpcode i
  | .copy x y => 0xFC :: toOpcode (14 : Unsigned32) ++ toOpcode x ++ toOpcode y
  | .init x y => 0xFC :: toOpcode (12 : Unsigned32) ++ toOpcode y ++ toOpcode x

nonrec def Table.ofOpcode : Bytecode Table :=
  Bytecode.err_log "Parsing table instruction." do
  match ← Bytecode.readByte with
  | 0x25 => return Table.get (← ofOpcode)
  | 0x26 => return Table.set (← ofOpcode)
  | 0xFC =>
    let v : Unsigned32 ← ofOpcode
    if v = 12 then
      let y ← ofOpcode
      let x ← ofOpcode
      return .init x y
    if v = 14 then
      let x ← ofOpcode
      let y ← ofOpcode
      return .copy x y
    if v = 15 then return Table.grow (← ofOpcode)
    if v = 16 then return Table.size (← ofOpcode)
    if v = 17 then return Table.fill (← ofOpcode)
    Bytecode.err
  | _ => Bytecode.err

instance : Opcode Table := ⟨Table.toOpcode, Table.ofOpcode⟩

namespace Memory
open Memory

nonrec def Arg.toOpcode (arg : Arg) : ByteSeq :=
  toOpcode arg.align ++ toOpcode arg.offset
nonrec def Arg.ofOpcode : Bytecode Arg :=
  Bytecode.err_log "Parsing memory arg." do
  let a ← ofOpcode
  let o ← ofOpcode
  return ⟨a, o⟩
instance : Opcode Arg := ⟨Arg.toOpcode, Arg.ofOpcode⟩


nonrec def Integer.toOpcode : Integer nn → ByteSeq
  | .load a      =>
    match nn with | .double => 0x28 :: toOpcode a | .quad => 0x29 :: toOpcode a
  | .store a     =>
    match nn with | .double => 0x36 :: toOpcode a | .quad => 0x37 :: toOpcode a
  | .load8 .s a  =>
    match nn with | .double => 0x2C :: toOpcode a | .quad => 0x30 :: toOpcode a
  | .load8 .u a  =>
    match nn with | .double => 0x2D :: toOpcode a | .quad => 0x31 :: toOpcode a
  | .load16 .s a =>
    match nn with | .double => 0x2E :: toOpcode a | .quad => 0x32 :: toOpcode a
  | .load16 .u a =>
    match nn with | .double => 0x2F :: toOpcode a | .quad => 0x33 :: toOpcode a
  | .load32 .s a => 0x34 :: toOpcode a
  | .load32 .u a => 0x35 :: toOpcode a
  | .store8 a    =>
    match nn with | .double => 0x3A :: toOpcode a | .quad => 0x3C :: toOpcode a
  | .store16 a   =>
    match nn with | .double => 0x3B :: toOpcode a | .quad => 0x3D :: toOpcode a
  | .store32 a   => 0x3E :: toOpcode a

nonrec def Integer.ofOpcode : Bytecode (Integer nn) :=
  Bytecode.err_log s!"Parsing i{nn.toBits} memory instruction." do
  match nn with
  | .double =>
    match ← Bytecode.readByte with
    | 0x28 => return (Integer.load     ) (← ofOpcode)
    | 0x2C => return (Integer.load8  .s) (← ofOpcode)
    | 0x2D => return (Integer.load8  .u) (← ofOpcode)
    | 0x2E => return (Integer.load16 .s) (← ofOpcode)
    | 0x2F => return (Integer.load16 .u) (← ofOpcode)
    | 0x36 => return (Integer.store    ) (← ofOpcode)
    | 0x3A => return (Integer.store8   ) (← ofOpcode)
    | 0x3B => return (Integer.store16  ) (← ofOpcode)
    | _    => Bytecode.err
  | .quad   =>
    match ← Bytecode.readByte with
    | 0x29 => return (Integer.load     ) (← ofOpcode)
    | 0x30 => return (Integer.load8  .s) (← ofOpcode)
    | 0x31 => return (Integer.load8  .u) (← ofOpcode)
    | 0x32 => return (Integer.load16 .s) (← ofOpcode)
    | 0x33 => return (Integer.load16 .u) (← ofOpcode)
    | 0x34 => return (Integer.load32 .s) (← ofOpcode)
    | 0x35 => return (Integer.load32 .u) (← ofOpcode)
    | 0x37 => return (Integer.store    ) (← ofOpcode)
    | 0x3C => return (Integer.store8   ) (← ofOpcode)
    | 0x3D => return (Integer.store16  ) (← ofOpcode)
    | 0x3E => return (Integer.store32  ) (← ofOpcode)
    | _            => Bytecode.err

instance : Opcode (Integer nn) := ⟨Integer.toOpcode, Integer.ofOpcode⟩


nonrec def Float.toOpcode : Float nn → ByteSeq
  | .load a  =>
    match nn with | .double => 0x2A :: toOpcode a | .quad => 0x2B :: toOpcode a
  | .store a =>
    match nn with | .double => 0x38 :: toOpcode a | .quad => 0x39 :: toOpcode a

nonrec def Float.ofOpcode : Bytecode (Float nn) :=
  Bytecode.err_log s!"Parsing f{nn.toBits} memory instruction." do
  match nn with
  | .double =>
    match ← Bytecode.readByte with
    | 0x2A => return Float.load  (← ofOpcode)
    | 0x38 => return Float.store (← ofOpcode)
    | _    => Bytecode.err
  | .quad   =>
    match ← Bytecode.readByte with
    | 0x2B => do return Float.load  (← ofOpcode)
    | 0x39 => do return Float.store (← ofOpcode)
    | _    => Bytecode.err

instance : Opcode (Float nn) := ⟨Float.toOpcode, Float.ofOpcode⟩

end Memory

nonrec def Memory.toOpcode : Memory → ByteSeq
  | .integer i   => toOpcode i
  | .float f     => toOpcode f
  | .size        => [0x3F, 0x00]
  | .grow        => [0x40, 0x00]
  | .fill        => 0xFC :: toOpcode (11 : Unsigned32) ++ [0x00]
  | .copy        => 0xFC :: toOpcode (10 : Unsigned32) ++ [0x00, 0x00]
  | .init x      => 0xFC :: toOpcode ( 8 : Unsigned32) ++ toOpcode x ++ [0x00]
  | .data_drop x => 0xFC :: toOpcode ( 9 : Unsigned32) ++ toOpcode x

nonrec def Memory.ofOpcode : Bytecode Memory :=
  Bytecode.err_log "Parsing memory instruction." do
      (return (Memory.integer (nn := .double)) (← ofOpcode))
  <|> (return (Memory.integer (nn := .quad  )) (← ofOpcode))
  <|> (return (Memory.float   (nn := .double)) (← ofOpcode))
  <|> (return (Memory.float   (nn := .quad  )) (← ofOpcode))
  <|> ( do match ← Bytecode.readByte with
        | 0x3F =>
          match ← Bytecode.readByte with
          | 0x00 => return .size
          | _    => Bytecode.err
        | 0x40 =>
          match ← Bytecode.readByte with
          | 0x00 => return .grow
          | _    => Bytecode.err
        | 0xFC => do
          let v ← ofOpcode
          if v = 11 then
            match ← Bytecode.readByte with
            | 0x00 => return .fill
            | _    => Bytecode.err
          else if v = 10 then
            match ← Bytecode.readByte with
            | 0x00 =>
              match ← Bytecode.readByte with
              | 0x00 => return .copy
              | _    => Bytecode.err
            | _    => Bytecode.err
          else if v = 9 then
            return Memory.data_drop (← ofOpcode)
          else if v = 8 then
            let x ← ofOpcode
            match ← Bytecode.readByte with
            | 0x00 => return .init x
            | _    => Bytecode.err
          else Bytecode.err
        | _ => Bytecode.err
  )

instance : Opcode Memory := ⟨Memory.toOpcode, Memory.ofOpcode⟩

end Instr

open Wasm.Syntax

mutual
def Instr.toOpcode : Wasm.Syntax.Instr → ByteSeq
  | .numeric n                => Instr.Numeric.toOpcode n
  | .reference r              => Instr.Reference.toOpcode r
  -- Parametric
  | .drop                     => 0x1A :: []
  | .select .none             => 0x1B :: []
  | .select (.some t)         => 0x1C :: List.toOpcode t
  | .locl l                   => Instr.Local.toOpcode l
  | .globl g                  => Instr.Global.toOpcode g
  | .table t                  => Instr.Table.toOpcode t
  | .elem_drop e              =>
    0xFC :: Wasm.Binary.Opcode.toOpcode (13 : Unsigned32)
      ++ Wasm.Binary.Opcode.toOpcode e
  | .memory m                 => Instr.Memory.toOpcode m
  -- Control
  | .nop                      => 0x01 :: []
  | .unreachable              => 0x00 :: []
  | .block bt is en           =>
    0x02 :: BlockType.toOpcode bt ++ listToOpcode is ++ [Pseudo.toOpcode en]
  | .loop bt is en            =>
    0x03 :: BlockType.toOpcode bt ++ listToOpcode is ++ [Pseudo.toOpcode en]
  | .wasm_if bt is₁ _el [] en  =>
    0x04 :: BlockType.toOpcode bt ++ listToOpcode is₁ ++ [Pseudo.toOpcode en]
  | .wasm_if bt is₁ el is₂ en =>
    0x04 :: BlockType.toOpcode bt
      ++ listToOpcode is₁
      ++ [Pseudo.toOpcode el]
      ++ listToOpcode is₂
      ++ [Pseudo.toOpcode en]
  | .br l                     => 0x0C :: Wasm.Binary.Opcode.toOpcode l
  | .br_if l                  => 0x0D :: Wasm.Binary.Opcode.toOpcode l
  | .br_table ls l            =>
    0x0E :: Vec.toOpcode ls ++ Wasm.Binary.Opcode.toOpcode l
  | .wasm_return              => 0x0F :: []
  | .call f                   => 0x10 :: Wasm.Binary.Opcode.toOpcode f
  | .call_indirect x y        =>
    0x11 :: Wasm.Binary.Opcode.toOpcode y ++ Wasm.Binary.Opcode.toOpcode x

def Instr.listToOpcode : List Wasm.Syntax.Instr → ByteSeq
  | [] => []
  | i :: is => Instr.toOpcode i ++ listToOpcode is
end
termination_by
  Instr.toOpcode i      => sizeOf i
  Instr.listToOpcode is => sizeOf is

mutual
private def Instr.ofOpcodeAux (pos : Nat) : Bytecode Wasm.Syntax.Instr :=
  Bytecode.err_log "Parsing instruction." do
      (return (Instr.numeric (nn := .double)) (← Numeric.ofOpcode))
  <|> (return (Instr.numeric (nn := .quad  )) (← Numeric.ofOpcode))
  <|> (return (Instr.reference              ) (← Reference.ofOpcode))
  <|> (return (Instr.locl                   ) (← Local.ofOpcode))
  <|> (return (Instr.globl                  ) (← Global.ofOpcode))
  <|> (return (Instr.table                  ) (← Table.ofOpcode))
  <|> (return (Instr.memory                 ) (← Memory.ofOpcode))
  <|> (do match ← Bytecode.readByte with
          | 0x00 => return .unreachable
          | 0x01 => return .nop
          | 0x02 =>
            let bt ← BlockType.ofOpcode

            let bytes ← get
            let pos' := bytes.length
            if h : pos' ≥ pos then Bytecode.errMsg "Illegal backtracking." else
            have : List.length bytes < pos := by simp at h; exact h

            let is ← Instr.listOfOpcodeAux pos'
            let e  ← Pseudo.ofOpcode
            match e with
            | .wasm_end => return .block bt is e
            | _         => Bytecode.err
          | 0x03 =>
            let bt ← BlockType.ofOpcode

            let bytes ← get
            let pos' := bytes.length
            if h : pos' ≥ pos then Bytecode.errMsg "Illegal backtracking." else
            have : List.length bytes < pos := by simp at h; exact h

            let is ← Instr.listOfOpcodeAux pos'
            let e  ← Pseudo.ofOpcode
            match e with
            | .wasm_end => return .loop bt is e
            | _         => Bytecode.err
          | 0x04 =>
            let bt  ← BlockType.ofOpcode

            let bytes ← get
            let pos' := bytes.length
            if h : pos' ≥ pos then Bytecode.errMsg "Illegal backtracking." else
            have : List.length bytes < pos := by simp at h; exact h

            let is₁ ← Instr.listOfOpcodeAux pos'
            let e₁  ← Pseudo.ofOpcode
            match e₁ with
            | .wasm_end  => return .wasm_if bt is₁ .wasm_else [] e₁
            | .wasm_else =>
              let bytes ← get
              let pos' := bytes.length
              if h : pos' ≥ pos then Bytecode.errMsg "Illegal backtracking." else
              have : List.length bytes < pos := by simp at h; exact h

              let is₂ ← Instr.listOfOpcodeAux pos'
              let e₂  ← Pseudo.ofOpcode
              match e₂ with
              | .wasm_end => return .wasm_if bt is₁ e₁ is₂ e₂
              | _         => Bytecode.err
          | 0x0C => return .br (← Wasm.Binary.Opcode.ofOpcode)
          | 0x0D => return .br_if (← Wasm.Binary.Opcode.ofOpcode)
          | 0x0E => do
            let t ← Vec.ofOpcode
            let l ← Wasm.Binary.Opcode.ofOpcode
            return .br_table t l
          | 0x0F => return .wasm_return
          | 0x10 => return .call (← Wasm.Binary.Opcode.ofOpcode)
          | 0x11 => do
            let y ← Wasm.Binary.Opcode.ofOpcode
            let x ← Wasm.Binary.Opcode.ofOpcode
            return .call_indirect x y
          | 0x1A => return .drop
          | 0x1B => return .select .none
          | 0x1C => return .select (.some (← Vec.ofOpcode).list)
          | 0xFC => do
            let v ← Wasm.Binary.Opcode.ofOpcode
            let x ← Wasm.Binary.Opcode.ofOpcode
            if v = 13 then return .elem_drop x
            Bytecode.err
          | _ => Bytecode.err
  )

def Instr.listOfOpcodeAux (pos : Nat) : Bytecode (List Wasm.Syntax.Instr) := do
  match ← get with
  | 0x0B :: _ => return []
  | 0x05 :: _ => return []
  | _  => do
    let bytes ← get
    let pos' := bytes.length
    if h : pos' ≥ pos then Bytecode.errMsg "Illegal backtracking." else
    have : List.length bytes < pos := by simp at h; exact h

    let i ← Instr.ofOpcodeAux pos'

    let bytes ← get
    let pos' := bytes.length
    if h : pos' ≥ pos then Bytecode.errMsg "Illegal backtracking." else
    have : List.length bytes < pos := by simp at h; exact h

    let is ← Instr.listOfOpcodeAux pos'
    return is ++ [i]
end
termination_by
  Instr.ofOpcodeAux p     => p
  Instr.listOfOpcodeAux p => p

def Instr.ofOpcode : Bytecode Wasm.Syntax.Instr := do
  let bytes ← get
  Instr.ofOpcodeAux (bytes.length)


instance : Opcode Instr := ⟨Instr.toOpcode, Instr.ofOpcode⟩


nonrec def Expr.toOpcode (expr : Expr) : ByteSeq :=
  Instr.listToOpcode expr.1 ++ [Instr.Pseudo.toOpcode expr.2]

nonrec def Expr.ofOpcode : Bytecode Wasm.Syntax.Expr :=
  Bytecode.err_log "Parsing expression." do
  let bytes ← get
  let is ← Instr.listOfOpcodeAux bytes.length
  let e  ← Instr.Pseudo.ofOpcode
  match e with
  | .wasm_end => return (is, e)
  | _         => Bytecode.err

instance : Opcode Expr := ⟨Expr.toOpcode, Expr.ofOpcode⟩
