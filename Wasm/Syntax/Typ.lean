/- Encoding of defintion WASM's type defintion:
    https://webassembly.github.io/spec/core/syntax/types.html
-/
import Wasm.Util
import Wasm.Binary.Opcode

namespace Wasm.Syntax.Typ

inductive Num
| i32
| i64
| f32
| f64
deriving DecidableEq, Inhabited

inductive Vec
| v128
deriving DecidableEq, Inhabited

inductive Ref
| func
| extern
deriving DecidableEq, Inhabited

inductive Val
| num : Num → Val
| vec : Vec → Val
| ref : Ref → Val
deriving DecidableEq, Inhabited

@[inline] def Result := Wasm.Vec Val
deriving DecidableEq, Inhabited

structure Func where
  args   : Result
  result : Result
deriving DecidableEq, Inhabited

structure Limit where
  min : UInt32 -- number of page sizes
  max : Option UInt32

@[inline] def Mem := Limit
@[inline] def Table := Limit × Ref

inductive Mut
| const
| var

def Global := Mut × Val

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
