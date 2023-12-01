import Wasm.Vec
import Wasm.Syntax.Instr
import Wasm.Syntax.Typ
import Wasm.Dynamics.Address
import Wasm.Dynamics.Instr
import Numbers
open Numbers

namespace Wasm.Dynamics

open Wasm.Syntax
open Syntax.Instr

inductive Value.Numeric
| int_const   : (nn : Numeric.Size)
              → {v : Unsigned (Numeric.Size.toBits nn)}
              → {i : Instr.Dynamic // i = .real (.numeric (.integer (.const v)))}
              → Value.Numeric
| float_const : (nn : Numeric.Size)
              → {v : Value.FloatN (Numeric.Size.toBits nn)}
              → {i : Instr.Dynamic // i = .real (.numeric (.float (.const v) : Instr.Numeric nn))}
              → Value.Numeric

inductive Value.Vec : Type
-- todo Vectors

-- Instr.Dynamic
inductive Value.Reference
| null        : {i : Instr.Dynamic // i = .real (.reference (.null t))} → Value.Reference
| ref         : {i : Instr.Dynamic // i = .admin (.ref addr)} → Value.Reference
| ref_extern  : {i : Instr.Dynamic // i = .admin (.ref_extern addr)} → Value.Reference

inductive Value
| num : Value.Numeric → Value
| vec : Value.Vec → Value
| ref : Value.Reference → Value

def Value.instr : Value → Instr.Dynamic
| .num (.int_const _ instr)   => instr
| .num (.float_const _ instr) => instr
| .ref (.null instr)          => instr
| .ref (.ref instr)           => instr
| .ref (.ref_extern instr)    => instr

def Value.type : Value → Syntax.Typ.Val
| .num (.int_const .double _instr)   => .num .i32
| .num (.int_const .quad _instr)     => .num .i64
| .num (.float_const .double _instr) => .num .f32
| .num (.float_const .quad _instr)   => .num .f64
| .vec _                             => .vec .v128
| .ref (.null _instr)                => .ref .func
| .ref (.ref _instr)                 => .ref .func
| .ref (.ref_extern _instr)          => .ref .extern

def Value.default : Typ.Val → Instr.Dynamic
  | .num n =>
    match n with
    | .i32 => .real <| .numeric
        (.integer (.const ⟨0, by simp⟩) : Instr.Numeric .double)
    | .i64 => .real <| .numeric
        (.integer (.const ⟨0, by simp⟩) : Instr.Numeric .quad)
    | .f32 => .real <| .numeric
        (.float (.const (Float.ofNat 0)) : Instr.Numeric .double)
    | .f64 => .real <| .numeric
        (.float (.const (Float.ofNat 0)) : Instr.Numeric .quad)
  | .vec v => .admin .trap          -- todo vector
  | .ref r => .real <| .reference (.null r)

inductive Value.Result : Prop
| result : List Value → Result
| trap

inductive Value.Extern
| func  : Address.Function → Extern
| table : Address.Table → Extern
| mem   : Address.Memory → Extern
| globl : Address.Global → Extern

def Value.funcs (vals : List Value.Extern) : List Address.Function :=
  vals.filterMap (fun v =>
    match v with
    | .func addr => .some addr
    | _          => .none
  )
def Value.tables (vals : List Value.Extern) : List Address.Table :=
  vals.filterMap (fun v =>
    match v with
    | .table addr => .some addr
    | _           => .none
  )
def Value.mems (vals : List Value.Extern) : List Address.Memory :=
  vals.filterMap (fun v =>
    match v with
    | .mem addr => .some addr
    | _         => .none
  )
def Value.global (vals : List Value.Extern) : List Address.Global :=
  vals.filterMap (fun v =>
    match v with
    | .globl addr => .some addr
    | _           => .none
  )

inductive IsValue : Instr.Dynamic → Value → Prop
| int_const   : IsValue instr.val (.num (.int_const nn instr))
| float_const : IsValue instr.val (.num (.float_const nn instr))
-- todo Vectors
| null        : IsValue instr.val (.ref (.null instr))
| ref         : IsValue instr.val (.ref (.ref instr))
| ref_extern  : IsValue instr.val (.ref (.ref_extern instr))
