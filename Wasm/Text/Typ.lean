/- Encoding of defintion WASM's type defintion:
    https://webassembly.github.io/spec/core/text/types.html#
-/
import Wasm.Util
import Wasm.Syntax.Typ
import Wasm.Text.Context

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

end Syntax.Typ

namespace Text.Typ

-- For some reason the text section defines a heaptype, which is the same as
--    as a reftype.
def Heap := Syntax.Typ.Ref
instance : ToString Heap := ⟨Syntax.Typ.Ref.toString⟩


def Param := Option Ident × Syntax.Typ.Val
def Param.toString : Param → String
  | (.some id, v) => s!"(param {id} {v})"
  | (.none, v)    => s!"(param {v})"
instance : Coe Syntax.Typ.Result (Vec Param) := ⟨(·.map ((.none, ·)))⟩

instance : ToString Param := ⟨Param.toString⟩
instance : ToString (List Param) := ⟨String.concatWith " "⟩
instance : ToString (Vec Param) := ⟨String.concatWith " " ∘ Vec.list⟩


def Result := Syntax.Typ.Val
instance : Coe Syntax.Typ.Result (Vec Result) := ⟨(·)⟩

instance : ToString Result := ⟨fun v => v.toString⟩
instance : ToString (List Result) := ⟨String.concatWith " "⟩
instance : ToString (Vec Result) := ⟨String.concatWith " " ∘ Vec.list⟩


structure Func where
  args   : Vec Param
  result : Vec Result
instance : Coe Syntax.Typ.Func Func := ⟨fun f => ⟨f.args, f.result⟩⟩

instance : ToString Func := ⟨fun f => s!"(func {f.args} {f.result})"⟩
instance : ToString Syntax.Typ.Func :=
  ⟨(fun f => toString (Func.mk f.args f.result))⟩
