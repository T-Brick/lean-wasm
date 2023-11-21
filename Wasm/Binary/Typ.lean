/- Encoding of defintion WASM's type defintion:
    https://webassembly.github.io/spec/core/binary/types.html
-/
import Wasm.Util
import Wasm.Binary.Opcode
import Wasm.Syntax.Typ

namespace Wasm.Syntax.Typ

def Num.toOpcode : Num → UInt8
  | .i32 => 0x7F
  | .i64 => 0x7E
  | .f32 => 0x7D
  | .f64 => 0x7C
instance : ToOpcode Num := ⟨Num.toOpcode⟩

def Vec.toOpcode : Syntax.Typ.Vec → UInt8
  | .v128 => 0x7B
instance : ToOpcode Syntax.Typ.Vec := ⟨Vec.toOpcode⟩

def Ref.toOpcode : Ref → UInt8
  | .func   => 0x70
  | .extern => 0x6F
instance : ToOpcode Ref := ⟨Ref.toOpcode⟩

def Val.toOpcode : Val → UInt8
  | .num v => v.toOpcode
  | .vec v => v.toOpcode
  | .ref v => v.toOpcode
instance : ToOpcode Val := ⟨Val.toOpcode⟩

-- todo Result + Func

-- todo Limit + Mem + Table

-- todo Global

-- todo Extern
