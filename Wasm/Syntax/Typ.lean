/- Encoding of defintion WASM's type defintion:
    https://webassembly.github.io/spec/core/syntax/types.html
-/
import Wasm.Util
import Wasm.Syntax.Opcode

namespace Wasm.Syntax.Typ

inductive Num
| i32
| i64
| f32
| f64

def Num.toString : Num → String
  | .i32 => "i32"
  | .i64 => "i64"
  | .f32 => "f32"
  | .f64 => "f64"
instance : ToString Num := ⟨Num.toString⟩

def Num.toOpcode : Num → UInt8
  | .i32 => 0x7F
  | .i64 => 0x7E
  | .f32 => 0x7D
  | .f64 => 0x7C
instance : ToOpcode Num := ⟨Num.toOpcode⟩

inductive Vec
| v128

def Vec.toString : Vec → String
  | .v128 => "v128"
instance : ToString Vec := ⟨Vec.toString⟩

def Vec.toOpcode : Vec → UInt8
  | .v128 => 0x7B
instance : ToOpcode Vec := ⟨Vec.toOpcode⟩

inductive Ref
| func
| extern

def Ref.toString : Ref → String
  | .func   => "funcref"
  | .extern => "externref"
instance : ToString Ref := ⟨Ref.toString⟩

def Ref.toOpcode : Ref → UInt8
  | .func   => 0x70
  | .extern => 0x6F
instance : ToOpcode Ref := ⟨Ref.toOpcode⟩

inductive Val
| num : Num → Val
| vec : Vec → Val
| ref : Ref → Val

def Val.toString : Val → String
  | .num v => v.toString
  | .vec v => v.toString
  | .ref v => v.toString
instance : ToString Val := ⟨Val.toString⟩

def Val.toOpcode : Val → UInt8
  | .num v => v.toOpcode
  | .vec v => v.toOpcode
  | .ref v => v.toOpcode
instance : ToOpcode Val := ⟨Val.toOpcode⟩

@[inline] def Result := List Val
structure Func where
  args   : Result
  result : Result

nonrec def Func.toString (func : Func) : String :=
  let args := String.concatWith " " (func.args.map (fun a => s!"(param {a})"))
  let res  := String.concatWith " " (func.result.map (fun r => s!"(result {r})"))
  s!"(func ({args}) ({res}))"
instance : ToString Func := ⟨Func.toString⟩


structure Limit where
  min : UInt32 -- number of page sizes
  max : Option UInt32

def Limit.toString (lim : Limit) : String :=
  match lim.max with
  | .none => s!"{lim.min}"
  | .some m => s!"{lim.min} {m}"
instance : ToString Limit := ⟨Limit.toString⟩

@[inline] def Mem := Limit
instance : ToString Mem := ⟨Limit.toString⟩

@[inline] def Table := Limit × Ref
instance : ToString Table := ⟨fun (lim, ref) => s!"{lim} {ref}"⟩

inductive Mut
| const
| var

def Global := Mut × Val

nonrec def Global.toString (glb : Global) : String :=
  let (m, v) := glb
  match m with
  | .const => toString v
  | .var   => s!"(mut {v})"
instance : ToString Global := ⟨Global.toString⟩

inductive Extern
| func  : Func → Extern
| table : Table → Extern
| mem   : Mem → Extern
| globl : Global → Extern

def Extern.funcs (externs : List Extern) : List Func :=
  externs.filterMap (fun extern =>
    match extern with
    | .func f => .some f
    | _       => .none
  )

def Extern.tables (externs : List Extern) : List Table :=
  externs.filterMap (fun extern =>
    match extern with
    | .table t => .some t
    | _        => .none
  )

def Extern.mems (externs : List Extern) : List Mem :=
  externs.filterMap (fun extern =>
    match extern with
    | .mem m => .some m
    | _      => .none
  )

def Extern.globals (externs : List Extern) : List Global :=
  externs.filterMap (fun extern =>
    match extern with
    | .globl g => .some g
    | _        => .none
  )

