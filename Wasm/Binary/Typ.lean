/- Encoding of defintion WASM's type defintion:
    https://webassembly.github.io/spec/core/binary/types.html
-/
import Wasm.Util
import Wasm.Binary.Opcode
import Wasm.Syntax.Typ

namespace Wasm.Binary.Typ

open Wasm.Syntax.Typ

def Num.toOpcode : Syntax.Typ.Num → Byte
  | .i32 => 0x7F
  | .i64 => 0x7E
  | .f32 => 0x7D
  | .f64 => 0x7C

def Num.ofOpcode : Bytecode Syntax.Typ.Num := do
  match ← Bytecode.readByte with
  | 0x7F => return .i32
  | 0x7E => return .i64
  | 0x7D => return .f32
  | 0x7C => return .f64
  | _    => Bytecode.errMsg "Parsing numtype."

instance : Opcode Syntax.Typ.Num := ⟨Byte.toSeq ∘ Num.toOpcode, Num.ofOpcode⟩


def Vec.toOpcode : Syntax.Typ.Vec → UInt8
  | .v128 => 0x7B

def Vec.ofOpcode : Bytecode Syntax.Typ.Vec := do
  match ← Bytecode.readByte with
  | 0x7B => return .v128
  | _    => Bytecode.errMsg "Parsing vectype."

instance : Opcode Syntax.Typ.Vec := ⟨Byte.toSeq ∘ Vec.toOpcode, Vec.ofOpcode⟩


def Ref.toOpcode : Ref → UInt8
  | .func   => 0x70
  | .extern => 0x6F

def Ref.ofOpcode : Bytecode Ref := do
  match ← Bytecode.readByte with
  | 0x70 => return .func
  | 0x6F => return .extern
  | _    => Bytecode.errMsg "Parsing vectype."

instance : Opcode Ref := ⟨Byte.toSeq ∘ Ref.toOpcode, Ref.ofOpcode⟩


def Val.toOpcode : Val → UInt8
  | .num v => Num.toOpcode v
  | .vec v => Vec.toOpcode v
  | .ref v => Ref.toOpcode v

def Val.ofOpcode : Bytecode Val :=
  Bytecode.err_log "Parsing valtype." do
      (return Val.num (← Num.ofOpcode))
  <|> (return Val.vec (← Vec.ofOpcode))
  <|> (return Val.ref (← Ref.ofOpcode))

instance : Opcode Val := ⟨Byte.toSeq ∘ Val.toOpcode, Val.ofOpcode⟩


def Result.toOpcode (res : Result) : ByteSeq := Wasm.Binary.Vec.toOpcode res
def Result.ofOpcode : Bytecode Result        := Wasm.Binary.Vec.ofOpcode
instance : Opcode Result := ⟨Result.toOpcode, Result.ofOpcode⟩


nonrec def Func.toOpcode (func : Func) : ByteSeq :=
  0x60 :: toOpcode func.args ++ toOpcode func.result

def Func.ofOpcode : Bytecode Func :=
  Bytecode.err_log "Parsing function type." do
  match ← Bytecode.readByte with
  | 0x60 =>
    let args ← Wasm.Binary.Vec.ofOpcode
    let res ← Wasm.Binary.Vec.ofOpcode
    return ⟨args, res⟩
  | _ => Bytecode.err

instance : Opcode Func := ⟨Func.toOpcode, Func.ofOpcode⟩


nonrec def Limit.toOpcode (lim : Limit) : ByteSeq :=
  match lim.max with
  | .none   => 0x00 :: toOpcode lim.min
  | .some m => 0x01 :: toOpcode lim.min ++ toOpcode m

nonrec def Limit.ofOpcode : Bytecode Limit :=
  Bytecode.err_log "Parsing limit." do
  match ← Bytecode.readByte with
  | 0x00 =>
    let min ← ofOpcode
    return ⟨min, .none⟩
  | 0x01 =>
    let min ← ofOpcode
    let max ← ofOpcode
    return ⟨min, .some max⟩
  | _ => Bytecode.err

instance : Opcode Limit := ⟨Limit.toOpcode, Limit.ofOpcode⟩
instance : Opcode Mem   := ⟨Limit.toOpcode, Limit.ofOpcode⟩


nonrec def Table.toOpcode (tab : Table) : ByteSeq :=
  toOpcode tab.2 ++ toOpcode tab.1

nonrec def Table.ofOpcode : Bytecode Table :=
  Bytecode.err_log "Parsing table type." do
  let ref ← Ref.ofOpcode
  let lim ← Limit.ofOpcode
  return ⟨lim, ref⟩

instance : Opcode Table := ⟨Table.toOpcode, Table.ofOpcode⟩

def Mut.toOpcode : Mut → Byte
  | .const => 0x00
  | .var   => 0x01

def Mut.ofOpcode : Bytecode Mut := do
  match ← Bytecode.readByte with
  | 0x00 => return .const
  | 0x01 => return .var
  | _    => Bytecode.errMsg "Parsing mutablility."

instance : Opcode Mut := ⟨Byte.toSeq ∘ Mut.toOpcode, Mut.ofOpcode⟩


nonrec def Global.toOpcode (g : Global) : ByteSeq :=
  toOpcode g.2 ++ toOpcode g.1

nonrec def Global.ofOpcode : Bytecode Global :=
  Bytecode.err_log "Parsing global type." do
  let val ← ofOpcode
  let m ← ofOpcode
  return (m, val)

instance : Opcode Global := ⟨Global.toOpcode, Global.ofOpcode⟩

-- todo Extern
