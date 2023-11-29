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

nonrec def BlockType.ofOpcode : ByteSeq → Option (BlockType × ByteSeq)
  | 0x40 :: rest => .some (.value .none, rest)
  | bytes =>
        (do (← Typ.Val.ofOpcode bytes) |>.map (BlockType.value ∘ .some) id)
    <|> (do let xb ← ofOpcode (α := Signed33) bytes
            if xb.1 ≥ 0 then
              return (.index (Unsigned.ofInt xb.1.toInt), xb.2)
            else .none
        )

instance : Opcode BlockType := ⟨BlockType.toOpcode, BlockType.ofOpcode⟩


def Pseudo.toOpcode : Pseudo → Byte
  | .wasm_end  => 0x0B
  | .wasm_else => 0x05

def Pseudo.ofOpcode : ByteSeq → Option (Pseudo × ByteSeq)
  | 0x0B :: rest => .some (.wasm_end, rest)
  | 0x05 :: rest => .some (.wasm_else, rest)
  | _            => .none

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

def Unop.ofOpcode32 : ByteSeq → Option (Unop × ByteSeq)
  | 0x67 :: rest => .some (.clz   , rest)
  | 0x68 :: rest => .some (.ctz   , rest)
  | 0x69 :: rest => .some (.popcnt, rest)
  | _            => .none
def Unop.ofOpcode64 : ByteSeq → Option (Unop × ByteSeq)
  | byte :: rest => Unop.ofOpcode32 ((byte - Unop.opcodeBitOffset) :: rest)
  | _            => .none


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

def Binop.ofOpcode32 : ByteSeq → Option (Binop × ByteSeq)
  | 0x6A :: rest => .some (.add   , rest)
  | 0x6B :: rest => .some (.sub   , rest)
  | 0x6C :: rest => .some (.mul   , rest)
  | 0x6D :: rest => .some (.div .s, rest)
  | 0x6E :: rest => .some (.div .u, rest)
  | 0x6F :: rest => .some (.rem .s, rest)
  | 0x70 :: rest => .some (.rem .u, rest)
  | 0x71 :: rest => .some (.and   , rest)
  | 0x72 :: rest => .some (.or    , rest)
  | 0x73 :: rest => .some (.xor   , rest)
  | 0x74 :: rest => .some (.shl   , rest)
  | 0x75 :: rest => .some (.shr .s, rest)
  | 0x76 :: rest => .some (.shr .u, rest)
  | 0x77 :: rest => .some (.rotl  , rest)
  | 0x78 :: rest => .some (.rotr  , rest)
  | _            => .none
def Binop.ofOpcode64 : ByteSeq → Option (Binop × ByteSeq)
  | byte :: rest => Binop.ofOpcode32 ((byte - Binop.opcodeBitOffset) :: rest)
  | _            => .none


def Test.toOpcode32 : Test → Byte | .eqz => 0x45
def Test.toOpcode64 : Test → Byte | .eqz => 0x50

def Test.ofOpcode32 : ByteSeq → Option (Test × ByteSeq)
  | 0x45 :: rest => .some (.eqz, rest)
  | _            => .none
def Test.ofOpcode64 : ByteSeq → Option (Test × ByteSeq)
  | 0x50 :: rest => .some (.eqz, rest)
  | _            => .none


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

def Relation.ofOpcode32 : ByteSeq → Option (Relation × ByteSeq)
  | 0x46 :: rest => .some (.eq   , rest)
  | 0x47 :: rest => .some (.ne   , rest)
  | 0x48 :: rest => .some (.lt .s, rest)
  | 0x49 :: rest => .some (.lt .u, rest)
  | 0x4A :: rest => .some (.gt .s, rest)
  | 0x4B :: rest => .some (.gt .u, rest)
  | 0x4C :: rest => .some (.le .s, rest)
  | 0x4D :: rest => .some (.le .u, rest)
  | 0x4E :: rest => .some (.ge .s, rest)
  | 0x4F :: rest => .some (.ge .u, rest)
  | _            => .none
def Relation.ofOpcode64 : ByteSeq → Option (Relation × ByteSeq)
  | byte :: rest =>
    Relation.ofOpcode32 ((byte - Relation.opcodeBitOffset) :: rest)
  | _            => .none


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

nonrec def ofOpcode : ByteSeq → Option (Integer nn × ByteSeq)
  | 0x41 :: rest =>
    match size_eq : nn with
    | .double => do
      let constb : (Signed nn.toBits) × ByteSeq ← ofOpcode rest
      let v := constb.1.toUnsignedN
      return (.const (cast (by rw [size_eq]) v), constb.2)
    | .quad   => .none
  | 0x42 :: rest =>
    match size_eq : nn with
    | .double => .none
    | .quad   => do
      let constb : (Signed nn.toBits) × ByteSeq ← ofOpcode rest
      let v := constb.1.toUnsignedN
      return (.const (cast (by rw [size_eq]) v), constb.2)
  | bytes =>
    match nn with
    | .double =>
          (do return (← Unop.ofOpcode32     bytes).map Integer.unop      id)
      <|> (do return (← Binop.ofOpcode32    bytes).map Integer.binop     id)
      <|> (do return (← Test.ofOpcode32     bytes).map Integer.test      id)
      <|> (do return (← Relation.ofOpcode32 bytes).map Integer.relation  id)
      <|> ( match bytes with
            | 0xA7 :: rest => .some (.wrap_i64          , rest)
            | 0xA8 :: rest => .some (.trunc_f .double .s, rest)
            | 0xA9 :: rest => .some (.trunc_f .double .u, rest)
            | 0xAA :: rest => .some (.trunc_f .quad   .s, rest)
            | 0xAB :: rest => .some (.trunc_f .quad   .u, rest)
            | 0xBC :: rest => .some (.reinterpret_f     , rest)
            | 0xC0 :: rest => .some (.extend8_s         , rest)
            | 0xC1 :: rest => .some (.extend16_s        , rest)
            | 0xFC :: rest => do
              let vb : Unsigned32 × ByteSeq ← ofOpcode rest
              if vb.1 = 0 then return (trunc_sat_f .double .s, vb.2)
              if vb.1 = 1 then return (trunc_sat_f .double .u, vb.2)
              if vb.1 = 2 then return (trunc_sat_f .quad   .s, vb.2)
              if vb.1 = 3 then return (trunc_sat_f .quad   .u, vb.2)
              none
            | _            => .none
          )
    | .quad   =>
          (do return (← Unop.ofOpcode64     bytes).map Integer.unop      id)
      <|> (do return (← Binop.ofOpcode64    bytes).map Integer.binop     id)
      <|> (do return (← Test.ofOpcode64     bytes).map Integer.test      id)
      <|> (do return (← Relation.ofOpcode64 bytes).map Integer.relation  id)
      <|> ( match bytes with
            | 0xAC :: rest => .some (.extend_i32 .s     , rest)
            | 0xAD :: rest => .some (.extend_i32 .u     , rest)
            | 0xAE :: rest => .some (.trunc_f .double .s, rest)
            | 0xAF :: rest => .some (.trunc_f .double .u, rest)
            | 0xB0 :: rest => .some (.trunc_f .quad   .s, rest)
            | 0xB1 :: rest => .some (.trunc_f .quad   .u, rest)
            | 0xBD :: rest => .some (.reinterpret_f     , rest)
            | 0xC2 :: rest => .some (.extend8_s         , rest)
            | 0xC3 :: rest => .some (.extend16_s        , rest)
            | 0xC4 :: rest => .some (.extend32_s        , rest)
            | 0xFC :: rest => do
              let vb : Unsigned32 × ByteSeq ← ofOpcode rest
              if vb.1 = 4 then return (trunc_sat_f .double .s, vb.2)
              if vb.1 = 5 then return (trunc_sat_f .double .u, vb.2)
              if vb.1 = 6 then return (trunc_sat_f .quad   .s, vb.2)
              if vb.1 = 7 then return (trunc_sat_f .quad   .u, vb.2)
              none
            | _            => .none
          )

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

def Unop.ofOpcode32 : ByteSeq → Option (Unop × ByteSeq)
  | 0x8B :: rest => .some (.abs    , rest)
  | 0x8C :: rest => .some (.neg    , rest)
  | 0x91 :: rest => .some (.sqrt   , rest)
  | 0x8D :: rest => .some (.ceil   , rest)
  | 0x8E :: rest => .some (.floor  , rest)
  | 0x8F :: rest => .some (.trunc  , rest)
  | 0x90 :: rest => .some (.nearest, rest)
  | _            => .none
def Unop.ofOpcode64 : ByteSeq → Option (Unop × ByteSeq)
  | byte :: rest => Unop.ofOpcode32 ((byte - Unop.opcodeBitOffset) :: rest)
  | _            => .none


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

def Binop.ofOpcode32 : ByteSeq → Option (Binop × ByteSeq)
  | 0x92 :: rest => .some (.add      ,rest)
  | 0x93 :: rest => .some (.sub      ,rest)
  | 0x94 :: rest => .some (.mul      ,rest)
  | 0x95 :: rest => .some (.div      ,rest)
  | 0x96 :: rest => .some (.min      ,rest)
  | 0x97 :: rest => .some (.max      ,rest)
  | 0x98 :: rest => .some (.copysign ,rest)
  | _            => .none
def Binop.ofOpcode64 : ByteSeq → Option (Binop × ByteSeq)
  | byte :: rest => Binop.ofOpcode32 ((byte - Binop.opcodeBitOffset) :: rest)
  | _            => .none


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

def Relation.ofOpcode32 : ByteSeq → Option (Relation × ByteSeq)
  | 0x5B :: rest => .some (.eq ,rest)
  | 0x5C :: rest => .some (.ne ,rest)
  | 0x5D :: rest => .some (.lt ,rest)
  | 0x5E :: rest => .some (.gt ,rest)
  | 0x5F :: rest => .some (.le ,rest)
  | 0x60 :: rest => .some (.ge ,rest)
  | _            => .none
def Relation.ofOpcode64 : ByteSeq → Option (Relation × ByteSeq)
  | byte :: rest =>
    Relation.ofOpcode32 ((byte - Relation.opcodeBitOffset) :: rest)
  | _            => .none

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

nonrec def ofOpcode : ByteSeq → Option (Float nn × ByteSeq)
  | 0x43 :: rest =>
    match _size_eq : nn with
    | .double => do
      let vb : (Wasm.Syntax.Value.FloatN nn.toBits) × ByteSeq ← ofOpcode rest
      return (.const vb.1, vb.2)
    | .quad   => .none
  | 0x44 :: rest =>
    match _size_eq : nn with
    | .double => .none
    | .quad   => do
      let vb : (Wasm.Syntax.Value.FloatN nn.toBits) × ByteSeq ← ofOpcode rest
      return (.const vb.1, vb.2)
  | bytes =>
    match nn with
    | .double =>
          (do return (← Unop.ofOpcode32     bytes).map Float.unop      id)
      <|> (do return (← Binop.ofOpcode32    bytes).map Float.binop     id)
      <|> (do return (← Relation.ofOpcode32 bytes).map Float.relation  id)
      <|> ( match bytes with
            | 0xB2 :: rest => .some (.convert_i .double .s, rest)
            | 0xB3 :: rest => .some (.convert_i .double .u, rest)
            | 0xB4 :: rest => .some (.convert_i .quad   .s, rest)
            | 0xB5 :: rest => .some (.convert_i .quad   .u, rest)
            | 0xB6 :: rest => .some (.demote_f64          , rest)
            | 0xBE :: rest => .some (.reinterpret_i       , rest)
            | _            => .none
          )
    | .quad   =>
          (do return (← Unop.ofOpcode64     bytes).map Float.unop      id)
      <|> (do return (← Binop.ofOpcode64    bytes).map Float.binop     id)
      <|> (do return (← Relation.ofOpcode64 bytes).map Float.relation  id)
      <|> ( match bytes with
            | 0xB7 :: rest => .some (.convert_i .double .s, rest)
            | 0xB8 :: rest => .some (.convert_i .double .u, rest)
            | 0xB9 :: rest => .some (.convert_i .quad   .s, rest)
            | 0xBA :: rest => .some (.convert_i .quad   .u, rest)
            | 0xBB :: rest => .some (.promote_f32         , rest)
            | 0xBF :: rest => .some (.reinterpret_i       , rest)
            | _            => .none
          )

instance : Opcode (Float nn) := ⟨toOpcode, ofOpcode⟩

end Float

def toOpcode : Numeric nn → ByteSeq
  | .integer i => Integer.toOpcode i
  | .float f   => Float.toOpcode f

def ofOpcode (seq : ByteSeq) : Option (Numeric nn × ByteSeq) :=
      (do return (← Integer.ofOpcode seq).map Numeric.integer id)
  <|> (do return (← Float.ofOpcode   seq).map Numeric.float   id)

instance : Opcode (Numeric nn) := ⟨toOpcode, ofOpcode⟩

end Numeric

nonrec def Reference.toOpcode : Reference → ByteSeq
  | .null t  => 0xD0 :: toOpcode t
  | .is_null => 0xD1 :: []
  | .func f  => 0xD2 :: toOpcode f

nonrec def Reference.ofOpcode : ByteSeq → Option (Reference × ByteSeq)
  | 0xD0 :: rest => do (← ofOpcode rest).map Reference.null id
  | 0xD1 :: rest => .some (.is_null, rest)
  | 0xD2 :: rest => do (← ofOpcode rest).map Reference.func id
  | _            => .none

instance : Opcode Reference := ⟨Reference.toOpcode, Reference.ofOpcode⟩


nonrec def Local.toOpcode : Local → ByteSeq
  | .get l => 0x20 :: toOpcode l
  | .set l => 0x21 :: toOpcode l
  | .tee l => 0x22 :: toOpcode l

nonrec def Local.ofOpcode : ByteSeq → Option (Local × ByteSeq)
  | 0x20 :: rest => do (← ofOpcode rest).map Local.get id
  | 0x21 :: rest => do (← ofOpcode rest).map Local.set id
  | 0x22 :: rest => do (← ofOpcode rest).map Local.tee id
  | _            => .none

instance : Opcode Local := ⟨Local.toOpcode, Local.ofOpcode⟩


nonrec def Global.toOpcode : Global → ByteSeq
  | .get l => 0x23 :: toOpcode l
  | .set l => 0x24 :: toOpcode l

nonrec def Global.ofOpcode : ByteSeq → Option (Global × ByteSeq)
  | 0x23 :: rest => do (← ofOpcode rest).map Global.get id
  | 0x24 :: rest => do (← ofOpcode rest).map Global.set id
  | _            => .none

instance : Opcode Global := ⟨Global.toOpcode, Global.ofOpcode⟩


nonrec def Table.toOpcode : Table → ByteSeq
  | .get i    => 0x25 :: toOpcode i
  | .set i    => 0x26 :: toOpcode i
  | .size i   => 0xFC :: toOpcode (16 : Unsigned32) ++ toOpcode i
  | .grow i   => 0xFC :: toOpcode (15 : Unsigned32) ++ toOpcode i
  | .fill i   => 0xFC :: toOpcode (17 : Unsigned32) ++ toOpcode i
  | .copy x y => 0xFC :: toOpcode (14 : Unsigned32) ++ toOpcode x ++ toOpcode y
  | .init x y => 0xFC :: toOpcode (12 : Unsigned32) ++ toOpcode y ++ toOpcode x

nonrec def Table.ofOpcode : ByteSeq → Option (Table × ByteSeq)
  | 0x25 :: rest => do (← ofOpcode rest).map Table.get id
  | 0x26 :: rest => do (← ofOpcode rest).map Table.set id
  | 0xFC :: rest => do
    let vb : Unsigned32 × ByteSeq ← ofOpcode rest
    if vb.1 = 12 then
      let yb ← ofOpcode vb.2
      let xb ← ofOpcode yb.2
      return (.init xb.1 yb.1, xb.2)
    if vb.1 = 14 then
      let xb ← ofOpcode vb.2
      let yb ← ofOpcode xb.2
      return (.copy xb.1 yb.1, yb.2)
    if vb.1 = 15 then return (← ofOpcode vb.2).map Table.grow id
    if vb.1 = 16 then return (← ofOpcode vb.2).map Table.size id
    if vb.1 = 17 then return (← ofOpcode vb.2).map Table.fill id
    none
  | _ => .none

instance : Opcode Table := ⟨Table.toOpcode, Table.ofOpcode⟩

namespace Memory
open Memory

nonrec def Arg.toOpcode (arg : Arg) : ByteSeq :=
  toOpcode arg.align ++ toOpcode arg.offset
nonrec def Arg.ofOpcode (seq : ByteSeq) : Option (Arg × ByteSeq) := do
  let ab ← ofOpcode seq
  let ob ← ofOpcode ab.2
  return (⟨ab.1, ob.1⟩, ob.2)
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

nonrec def Integer.ofOpcode (seq : ByteSeq) : Option (Integer nn × ByteSeq) :=
  match nn with
  | .double =>
    match seq with
    | 0x28 :: rest => do return (← ofOpcode rest).map (Integer.load     ) id
    | 0x2C :: rest => do return (← ofOpcode rest).map (Integer.load8  .s) id
    | 0x2D :: rest => do return (← ofOpcode rest).map (Integer.load8  .u) id
    | 0x2E :: rest => do return (← ofOpcode rest).map (Integer.load16 .s) id
    | 0x2F :: rest => do return (← ofOpcode rest).map (Integer.load16 .u) id
    | 0x36 :: rest => do return (← ofOpcode rest).map (Integer.store    ) id
    | 0x3A :: rest => do return (← ofOpcode rest).map (Integer.store8   ) id
    | 0x3B :: rest => do return (← ofOpcode rest).map (Integer.store16  ) id
    | _            => .none
  | .quad   =>
    match seq with
    | 0x29 :: rest => do return (← ofOpcode rest).map (Integer.load     ) id
    | 0x30 :: rest => do return (← ofOpcode rest).map (Integer.load8  .s) id
    | 0x31 :: rest => do return (← ofOpcode rest).map (Integer.load8  .u) id
    | 0x32 :: rest => do return (← ofOpcode rest).map (Integer.load16 .s) id
    | 0x33 :: rest => do return (← ofOpcode rest).map (Integer.load16 .u) id
    | 0x34 :: rest => do return (← ofOpcode rest).map (Integer.load32 .s) id
    | 0x35 :: rest => do return (← ofOpcode rest).map (Integer.load32 .u) id
    | 0x37 :: rest => do return (← ofOpcode rest).map (Integer.store    ) id
    | 0x3C :: rest => do return (← ofOpcode rest).map (Integer.store8   ) id
    | 0x3D :: rest => do return (← ofOpcode rest).map (Integer.store16  ) id
    | 0x3E :: rest => do return (← ofOpcode rest).map (Integer.store32  ) id
    | _            => .none

instance : Opcode (Integer nn) := ⟨Integer.toOpcode, Integer.ofOpcode⟩


nonrec def Float.toOpcode : Float nn → ByteSeq
  | .load a  =>
    match nn with | .double => 0x2A :: toOpcode a | .quad => 0x2B :: toOpcode a
  | .store a =>
    match nn with | .double => 0x38 :: toOpcode a | .quad => 0x39 :: toOpcode a

nonrec def Float.ofOpcode (seq : ByteSeq) : Option (Float nn × ByteSeq) :=
  match nn with
  | .double =>
    match seq with
    | 0x2A :: rest => do return (← ofOpcode rest).map Float.load  id
    | 0x38 :: rest => do return (← ofOpcode rest).map Float.store id
    | _            => .none
  | .quad   =>
    match seq with
    | 0x2B :: rest => do return (← ofOpcode rest).map Float.load  id
    | 0x39 :: rest => do return (← ofOpcode rest).map Float.store id
    | _            => .none

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

nonrec def Memory.ofOpcode : ByteSeq → Option (Memory × ByteSeq)
  | 0x3F :: 0x00 :: rest => .some (.size, rest)
  | 0x40 :: 0x00 :: rest => .some (.grow, rest)
  | 0xFC :: rest => do
    let vb ← ofOpcode rest
    if vb.1 = 11 then
      match vb.2 with
      | 0x00 :: rest => return (.fill, rest)
      | _            => none
    else if vb.1 = 10 then
      match vb.2 with
      | 0x00 :: 0x00 :: rest => return (.copy, rest)
      | _                    => none
    else if vb.1 = 9 then
      return (← ofOpcode rest).map Memory.data_drop id
    else if vb.1 = 8 then
      let xb ← ofOpcode rest
      match xb.2 with
      | 0x00 :: rest => return (.init xb.1, rest)
      | _            => none
    else none
  | seq =>
      (do (← ofOpcode seq).map (Memory.integer (nn := .double)) id)
  <|> (do (← ofOpcode seq).map (Memory.integer (nn := .quad  )) id)
  <|> (do (← ofOpcode seq).map (Memory.float   (nn := .double)) id)
  <|> (do (← ofOpcode seq).map (Memory.float   (nn := .quad  )) id)

instance : Opcode Memory := ⟨Memory.toOpcode, Memory.ofOpcode⟩

end Instr

open Wasm.Syntax

mutual
def Instr.toOpcode : Wasm.Syntax.Instr → ByteSeq
  | .numeric n                => Instr.Numeric.toOpcode n
  | .reference r              => Instr.Reference.toOpcode r
  -- Parametric => sorry
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
partial def Instr.ofOpcode : ByteSeq → Option (Wasm.Syntax.Instr × ByteSeq)
  | 0x00 :: rest => .some (.unreachable , rest)
  | 0x01 :: rest => .some (.nop         , rest)
  | 0x02 :: rest => do
    let btb ← BlockType.ofOpcode rest
    let isb ← Instr.listOfOpcode btb.2
    let eb  ← Pseudo.ofOpcode isb.2
    match eb.1 with
    | .wasm_end => return (.block btb.1 isb.1 eb.1, eb.2)
    | _         => none
  | 0x03 :: rest => do
    let btb ← BlockType.ofOpcode rest
    let isb ← Instr.listOfOpcode btb.2
    let eb  ← Pseudo.ofOpcode isb.2
    match eb.1 with
    | .wasm_end => return (.loop btb.1 isb.1 eb.1, eb.2)
    | _         => none
  | 0x04 :: rest => do
    let btb  ← BlockType.ofOpcode rest
    let is₁b ← Instr.listOfOpcode btb.2
    let e₁b  ← Pseudo.ofOpcode is₁b.2
    match e₁b.1 with
    | .wasm_end  => return (.wasm_if btb.1 is₁b.1 .wasm_else [] e₁b.1, e₁b.2)
    | .wasm_else =>
      let is₂b ← Instr.listOfOpcode e₁b.2
      let e₂b  ← Pseudo.ofOpcode is₂b.2
      match e₂b.1 with
      | .wasm_end => return (.wasm_if btb.1 is₁b.1 e₁b.1 is₂b.1 e₂b.1, e₂b.2)
      | _         => none
  | 0x0C :: rest => do
    let lb ← Wasm.Binary.Opcode.ofOpcode rest
    return (.br lb.1, lb.2)
  | 0x0D :: rest => do
    let lb ← Wasm.Binary.Opcode.ofOpcode rest
    return (.br_if lb.1, lb.2)
  | 0x0E :: rest => do
    let tb ← Vec.ofOpcode rest
    let lb ← Wasm.Binary.Opcode.ofOpcode tb.2
    return (.br_table tb.1 lb.1, lb.2)
  | 0x0F :: rest => .some (.wasm_return , rest)
  | 0x10 :: rest => do
    let fb ← Wasm.Binary.Opcode.ofOpcode rest
    return (.call fb.1, fb.2)
  | 0x11 :: rest => do
    let yb ← Wasm.Binary.Opcode.ofOpcode rest
    let xb ← Wasm.Binary.Opcode.ofOpcode yb.2
    return (.call_indirect xb.1 yb.1, xb.2)
  | 0x1A :: rest => .some (.drop        , rest)
  | 0x1B :: rest => .some (.select .none, rest)
  | 0x1C :: rest => do
    let tb ← Vec.ofOpcode rest
    return (.select (.some tb.1.list), tb.2)
  |  0xFC :: rest => do
    let vb ← Wasm.Binary.Opcode.ofOpcode rest
    let xb ← Wasm.Binary.Opcode.ofOpcode vb.2
    if vb.1 = 13 then return (.elem_drop xb.1, xb.2)
    none
  | seq =>
        (do (← Numeric.ofOpcode   seq).map (Instr.numeric (nn := .double)) id)
    <|> (do (← Numeric.ofOpcode   seq).map (Instr.numeric (nn := .quad  )) id)
    <|> (do (← Reference.ofOpcode seq).map (Instr.reference              ) id)
    <|> (do (← Local.ofOpcode     seq).map (Instr.locl                   ) id)
    <|> (do (← Global.ofOpcode    seq).map (Instr.globl                  ) id)
    <|> (do (← Table.ofOpcode     seq).map (Instr.table                  ) id)
    <|> (do (← Memory.ofOpcode    seq).map (Instr.memory                 ) id)


partial def Instr.listOfOpcode : ByteSeq → Option (List Wasm.Syntax.Instr × ByteSeq)
  | 0x0B :: rest => .some ([], 0x0B :: rest)
  | 0x05 :: rest => .some ([], 0x05 :: rest)
  | seq          => do
    let ib ← Instr.ofOpcode seq
    let isb ← listOfOpcode ib.2
    return (isb.1 ++ [ib.1], isb.2)
end

instance : Opcode Instr := ⟨Instr.toOpcode, Instr.ofOpcode⟩


nonrec def Expr.toOpcode (expr : Expr) : ByteSeq :=
  Instr.listToOpcode expr.1 ++ Instr.Pseudo.toOpcode expr.2
nonrec def Expr.ofOpcode (seq : ByteSeq) : Option (Expr × ByteSeq) := do
  let isb ← Instr.listOfOpcode seq
  let eb  ← Instr.Pseudo.ofOpcode isb.2
  match eb.1 with
  | .wasm_end => return ((isb.1, eb.1), eb.2)
  | _         => none

instance : Opcode Expr := ⟨Expr.toOpcode, Expr.ofOpcode⟩
