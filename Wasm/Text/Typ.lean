/- Encoding of defintion WASM's type defintion:
    https://webassembly.github.io/spec/core/text/types.html#
-/
import Wasm.Util
import Wasm.Syntax.Typ

namespace Wasm.Syntax.Typ

def Num.toString : Num → String
  | .i32 => "i32"
  | .i64 => "i64"
  | .f32 => "f32"
  | .f64 => "f64"
instance : ToString Num := ⟨Num.toString⟩

def Vec.toString : Syntax.Typ.Vec → String
  | .v128 => "v128"
instance : ToString Syntax.Typ.Vec := ⟨Vec.toString⟩

def Ref.toString : Ref → String
  | .func   => "funcref"
  | .extern => "externref"
instance : ToString Ref := ⟨Ref.toString⟩

def Val.toString : Val → String
  | .num v => v.toString
  | .vec v => v.toString
  | .ref v => v.toString
instance : ToString Val := ⟨Val.toString⟩

nonrec def Func.toString (func : Func) : String :=
  let args := String.concatWith " " (func.args.map (fun a => s!"(param {a})"))
  let res  := String.concatWith " " (func.result.map (fun r => s!"(result {r})"))
  s!"(func ({args}) ({res}))"
instance : ToString Func := ⟨Func.toString⟩

def Limit.toString (lim : Limit) : String :=
  match lim.max with
  | .none => s!"{lim.min}"
  | .some m => s!"{lim.min} {m}"
instance : ToString Limit := ⟨Limit.toString⟩
instance : ToString Mem := ⟨Limit.toString⟩

instance : ToString Table := ⟨fun (lim, ref) => s!"{lim} {ref}"⟩

nonrec def Global.toString (glb : Global) : String :=
  let (m, v) := glb
  match m with
  | .const => toString v
  | .var   => s!"(mut {v})"
instance : ToString Global := ⟨Global.toString⟩

-- todo Extern
