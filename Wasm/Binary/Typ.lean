/- Encoding of defintion WASM's type defintion:
    https://webassembly.github.io/spec/core/binary/types.html
-/
import Wasm.Util
import Wasm.Binary.Opcode
import Wasm.Syntax.Typ

namespace Wasm.Binary.Typ

open Wasm.Syntax.Typ

def Num.toOpcode : Num → UInt8
  | .i32 => 0x7F
  | .i64 => 0x7E
  | .f32 => 0x7D
  | .f64 => 0x7C

def Num.ofOpcode : ByteSeq → Option (Num × ByteSeq)
  | 0x7F :: rest => .some (.i32, rest)
  | 0x7E :: rest => .some (.i64, rest)
  | 0x7D :: rest => .some (.f32, rest)
  | 0x7C :: rest => .some (.f64, rest)
  | _            => .none

instance : Opcode Num := ⟨Byte.toSeq ∘ Num.toOpcode, Num.ofOpcode⟩


def Vec.toOpcode : Syntax.Typ.Vec → UInt8
  | .v128 => 0x7B

def Vec.ofOpcode : ByteSeq → Option (Syntax.Typ.Vec × ByteSeq)
  | 0x7B :: rest => .some  (.v128, rest)
  | _            => .none

instance : Opcode Syntax.Typ.Vec := ⟨Byte.toSeq ∘ Vec.toOpcode, Vec.ofOpcode⟩


def Ref.toOpcode : Ref → UInt8
  | .func   => 0x70
  | .extern => 0x6F

def Ref.ofOpcode : ByteSeq → Option (Ref × ByteSeq)
  | 0x70 :: rest => .some  (.func, rest)
  | 0x6F :: rest => .some  (.extern, rest)
  | _            => .none

instance : Opcode Ref := ⟨Byte.toSeq ∘ Ref.toOpcode, Ref.ofOpcode⟩


def Val.toOpcode : Val → UInt8
  | .num v => Num.toOpcode v
  | .vec v => Vec.toOpcode v
  | .ref v => Ref.toOpcode v

def Val.ofOpcode (seq : ByteSeq) : Option (Val × ByteSeq) :=
      (do (← Num.ofOpcode seq).map Val.num id)
  <|> (do (← Vec.ofOpcode seq).map Val.vec id)
  <|> (do (← Ref.ofOpcode seq).map Val.ref id)

instance : Opcode Val := ⟨Byte.toSeq ∘ Val.toOpcode, Val.ofOpcode⟩


def Result.toOpcode (res : Result) : ByteSeq := Wasm.Binary.Vec.toOpcode res
def Result.ofOpcode (seq : ByteSeq) : Option (Result × ByteSeq) :=
  Wasm.Binary.Vec.ofOpcode seq
instance : Opcode Result := ⟨Result.toOpcode, Result.ofOpcode⟩


nonrec def Func.toOpcode (func : Func) : ByteSeq :=
  0x60 :: toOpcode func.args ++ toOpcode func.result

def Func.ofOpcode : ByteSeq → Option (Func × ByteSeq)
  | 0x60 :: rest => do
    let argsb ← Wasm.Binary.Vec.ofOpcode rest
    let resb ← Wasm.Binary.Vec.ofOpcode argsb.2
    return (⟨argsb.1, resb.1⟩, resb.2)
  | _ => .none

instance : Opcode Func := ⟨Func.toOpcode, Func.ofOpcode⟩


nonrec def Limit.toOpcode (lim : Limit) : ByteSeq :=
  match lim.max with
  | .none   => 0x00 :: toOpcode lim.min
  | .some m => 0x01 :: toOpcode lim.min ++ toOpcode m

nonrec def Limit.ofOpcode : ByteSeq → Option (Limit × ByteSeq)
  | 0x00 :: rest => do
    let minb : Unsigned32 × ByteSeq ← ofOpcode rest
    return (⟨minb.1, .none⟩, minb.2)
  | 0x01 :: rest => do
    let minb : Unsigned32 × ByteSeq ← ofOpcode rest
    let maxb : Unsigned32 × ByteSeq ← ofOpcode minb.2
    return (⟨minb.1, .some maxb.1⟩, maxb.2)
  | _ => .none

instance : Opcode Limit := ⟨Limit.toOpcode, Limit.ofOpcode⟩
instance : Opcode Mem   := ⟨Limit.toOpcode, Limit.ofOpcode⟩


nonrec def Table.toOpcode (tab : Table) : ByteSeq :=
  toOpcode tab.2 ++ toOpcode tab.1

nonrec def Table.ofOpcode (bytes : ByteSeq) : Option (Table × ByteSeq) := do
  let refb ← Ref.ofOpcode bytes
  let limb ← Limit.ofOpcode refb.2
  return ((limb.1, refb.1), limb.2)

instance : Opcode Table := ⟨Table.toOpcode, Table.ofOpcode⟩

def Mut.toOpcode : Mut → Byte
  | .const => 0x00
  | .var   => 0x01

def Mut.ofOpcode : ByteSeq → Option (Mut × ByteSeq)
  | 0x00 :: rest => .some (.const, rest)
  | 0x01 :: rest => .some (.var, rest)
  | _            => .none

instance : Opcode Mut := ⟨Byte.toSeq ∘ Mut.toOpcode, Mut.ofOpcode⟩


nonrec def Global.toOpcode (g : Global) : ByteSeq :=
  toOpcode g.2 ++ toOpcode g.1

nonrec def Global.ofOpcode (bytes : ByteSeq) : Option (Global × ByteSeq) := do
  let valb ← ofOpcode bytes
  let mutb ← ofOpcode valb.2
  return ((mutb.1, valb.1), mutb.2)

instance : Opcode Global := ⟨Global.toOpcode, Global.ofOpcode⟩

-- todo Extern
