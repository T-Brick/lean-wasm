/- Encoding of defintion WASM's type defintion:
    https://webassembly.github.io/spec/core/text/types.html#
-/
import Wasm.Vec
import Wasm.Syntax.Typ
import Wasm.Text.Ident
import Wasm.Text.Trans

namespace Wasm

open Std

namespace Syntax.Typ

def Num.toString : Num → String
  | .i32 => "i32"
  | .i64 => "i64"
  | .f32 => "f32"
  | .f64 => "f64"
instance : ToString Num := ⟨Num.toString⟩
instance : ToFormat Num := ⟨Format.text ∘ Num.toString⟩

def Vec.toString : Syntax.Typ.Vec → String
  | .v128 => "v128"
instance : ToString Syntax.Typ.Vec := ⟨Vec.toString⟩
instance : ToFormat Syntax.Typ.Vec := ⟨Format.text ∘ Vec.toString⟩

def Ref.toString : Ref → String
  | .func   => "funcref"
  | .extern => "externref"
instance : ToString Ref := ⟨Ref.toString⟩
instance : ToFormat Ref := ⟨Format.text ∘ Ref.toString⟩

def Val.toString : Val → String
  | .num v => v.toString
  | .vec v => v.toString
  | .ref v => v.toString
instance : ToString Val := ⟨Val.toString⟩
instance : ToFormat Val := ⟨Format.text ∘ Val.toString⟩


def Limit.toString (lim : Limit) : String :=
  match lim.max with
  | .none => s!"{lim.min}"
  | .some m => s!"{lim.min} {m}"
instance : ToString Limit := ⟨Limit.toString⟩
instance : ToFormat Limit := ⟨Format.text ∘ Limit.toString⟩

instance : ToString Mem := ⟨Limit.toString⟩
instance : ToFormat Mem := ⟨Format.text ∘ Limit.toString⟩


instance : ToString Table := ⟨fun (lim, ref) => s!"{lim} {ref}"⟩

nonrec def Global.toString (glb : Global) : String :=
  let (m, v) := glb
  match m with
  | .const => toString v
  | .var   => s!"(mut {v})"
instance : ToString Global := ⟨Global.toString⟩
instance : ToFormat Global := ⟨Format.text ∘ Global.toString⟩

end Syntax.Typ

namespace Text.Typ

-- For some reason the text section defines a heaptype, which is the same as
--    as a reftype.
def Heap := Syntax.Typ.Ref
deriving DecidableEq, Inhabited, Repr

instance : ToString Heap := ⟨Syntax.Typ.Ref.toString⟩
instance : ToFormat Heap := ⟨Format.text ∘ Syntax.Typ.Ref.toString⟩


def Param := Option Ident × Syntax.Typ.Val
deriving DecidableEq, Inhabited

def Param.mk : Option Ident → Syntax.Typ.Val → Param := Prod.mk
def Param.toString : Param → String
  | (.some id, v) => s!"(param {id} {v})"
  | (.none, v)    => s!"(param {v})"
instance : Coe Syntax.Typ.Val Param := ⟨(.none, ·)⟩
instance : Coe Syntax.Typ.Result (Vec Param) := ⟨(·.map ((.none, ·)))⟩

instance : OfText Param Syntax.Typ.Val := ⟨(return ·.2)⟩
instance : OfText (Vec Param) Syntax.Typ.Result := ⟨(return ·.map (·.2))⟩

instance : ToString Param        := ⟨Param.toString⟩
instance : ToString (List Param) := ⟨String.concatWith " "⟩
instance : ToString (Vec Param)  := ⟨String.concatWith " " ∘ Vec.list⟩

instance : ToFormat Param := ⟨Format.text ∘ Param.toString⟩


def Result := Syntax.Typ.Val
deriving DecidableEq, Inhabited, Repr
instance : Coe Syntax.Typ.Result (Vec Result) := ⟨(·)⟩

instance : ToString Result := ⟨(s!"(result {·.toString})")⟩
instance : ToString (List Result) := ⟨String.concatWith " "⟩
instance : ToString (Vec Result) := ⟨String.concatWith " " ∘ Vec.list⟩


structure Func where
  args   : Vec Param
  result : Vec Result
deriving DecidableEq, Inhabited
instance : Coe Syntax.Typ.Func Func := ⟨fun f => ⟨f.args, f.result⟩⟩
instance : OfText Func Syntax.Typ.Func :=
  ⟨fun f => return ⟨← ofText f.args, f.result⟩⟩

instance : ToString Func := ⟨fun f => s!"(func {f.args} {f.result})"⟩
instance : ToString Syntax.Typ.Func :=
  ⟨(fun f => toString (Func.mk f.args f.result))⟩
