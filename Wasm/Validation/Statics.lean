/- https://webassembly.github.io/spec/core/valid/instructions.html -/

import Wasm.Syntax.Typ
import Wasm.Syntax.Index
import Wasm.Syntax.Value
import Wasm.Syntax.Instr
import Wasm.Validation.Context
import Wasm.Validation.Typ

namespace Wasm.Validation.Statics

open Syntax

inductive Typ.Operand
| bot
| val : Typ.Val → Operand

def toIntOpd (nn : Syntax.Instr.Numeric.Size): Typ.Operand :=
  .val (Syntax.Instr.Numeric.Size.toIntVal nn)

def toFloatOpd (nn : Syntax.Instr.Numeric.Size): Typ.Operand :=
  .val (Syntax.Instr.Numeric.Size.toFloatVal nn)

def i32 : Typ.Operand := .val (.num .i32)
def f32 : Typ.Operand := .val (.num .f32)
def i64 : Typ.Operand := .val (.num .i64)
def f64 : Typ.Operand := .val (.num .f64)
def ref (t : Typ.Ref) : Typ.Operand := .val (.ref t)


structure Typ.Stack where
  input  : List Typ.Operand
  output : List Typ.Operand

inductive Typ.MatchSingle : Typ.Operand → Typ.Operand → Prop
| refl  : Typ.MatchSingle t1 t2
| min   : Typ.MatchSingle .bot t

inductive Typ.MatchList : List Typ.Operand → List Typ.Operand → Prop
| empty : Typ.MatchList [] []
| cons  : Typ.MatchSingle t1 t2 → Typ.MatchList t1s t2s → Typ.MatchList (t1 :: t1s) (t2 :: t2s)

namespace Numeric

inductive Integer.Instr (Γ : Context) : Instr.Numeric.Integer nn → Typ.Stack → Prop
| const         : Instr Γ (.const v) ⟨[], [toIntOpd nn]⟩
| unop          : Instr Γ (.unop op) ⟨[toIntOpd nn], [toIntOpd nn]⟩
| binop         : Instr Γ (.binop op) ⟨[toIntOpd nn, toIntOpd nn], [toIntOpd nn]⟩
| test          : Instr Γ (.test op) ⟨[toIntOpd nn], []⟩
| relation      : Instr Γ (.relation op) ⟨[toIntOpd nn, toIntOpd nn], [i32]⟩
| extend8_s     : Instr Γ .extend8_s ⟨[i32], [toIntOpd nn]⟩
| extend16_s    : Instr Γ .extend16_s ⟨[i32], [toIntOpd nn]⟩
| extend32_s    : Instr Γ .extend32_s ⟨[i32], [toIntOpd nn]⟩
| wrap_i64      : Instr Γ .wrap_i64 ⟨[i64], [toIntOpd nn]⟩
| extend_i32    : Instr Γ (.extend_i32 s) ⟨[i32], [toIntOpd nn]⟩
| trunc_f       : Instr Γ (.trunc_f mm s) ⟨[toFloatOpd mm], [toIntOpd nn]⟩
| trunc_sat_f   : Instr Γ (.trunc_sat_f mm s) ⟨[toFloatOpd mm], [toIntOpd nn]⟩
| reinterpret_f : Instr Γ .reinterpret_f ⟨[toFloatOpd nn], [toIntOpd nn]⟩

inductive Float.Instr (Γ : Context) :  Instr.Numeric.Float nn → Typ.Stack → Prop
| const         : Instr Γ (.const v) ⟨[], [toFloatOpd nn]⟩
| unop          : Instr Γ (.unop op) ⟨[toFloatOpd nn], [toFloatOpd nn]⟩
| binop         : Instr Γ (.binop op) ⟨[toFloatOpd nn, toFloatOpd nn], [toFloatOpd nn]⟩
| relation      : Instr Γ (.relation op) ⟨[toFloatOpd nn, toFloatOpd nn], [i32]⟩
| demote_f64    : Instr Γ .demote_f64 ⟨[f64], [toFloatOpd nn]⟩
| promote_f32   : Instr Γ .promote_f32 ⟨[f32], [toFloatOpd nn]⟩
| convert_i     : Instr Γ (.convert_i mm s) ⟨[toIntOpd mm], [toFloatOpd nn]⟩
| reinterpret_i : Instr Γ .reinterpret_i  ⟨[toIntOpd nn], [toFloatOpd nn]⟩

inductive Instr (Γ : Context) : Instr.Numeric nn → Typ.Stack → Prop
| integer : Integer.Instr Γ instr type → Instr Γ (.integer instr) type
| float   : Float.Instr Γ instr type → Instr Γ (.float instr) type

end Numeric

-- todo vector instructions

inductive Reference.Instr (Γ : Context) : Instr.Reference → Typ.Stack → Prop
| null    : Instr Γ (.null t) ⟨[], [ref t]⟩
| is_null : Instr Γ .is_null ⟨[ref t], [i32]⟩
| func    : Γ.funcs.list.get x = f
          → Γ.refs.list.contains (Vec.index Γ.funcs x)
          → Instr Γ (.func (Vec.index Γ.funcs x)) ⟨[], [ref t]⟩

inductive Local.Instr (Γ : Context) : Instr.Local → Typ.Stack → Prop
| get : Γ.locals.list.get x = t
      → Instr Γ (.get (Vec.index Γ.locals x)) ⟨[], [.val t]⟩
| set : Γ.locals.list.get x = t
      → Instr Γ (.set (Vec.index Γ.locals x)) ⟨[.val t], []⟩
| tee : Γ.locals.list.get x = t
      → Instr Γ (.tee (Vec.index Γ.locals x)) ⟨[.val t], [.val t]⟩

inductive Global.Instr (Γ : Context) : Instr.Global → Typ.Stack → Prop
| get : Γ.globals.list.get x = (m, t)
      → Instr Γ (.get (Vec.index Γ.globals x)) ⟨[], [.val t]⟩
| set : Γ.globals.list.get x = (.var, t)
      → Instr Γ (.set (Vec.index Γ.globals x)) ⟨[.val t], []⟩

inductive Table.Instr (Γ : Context) : Instr.Table → Typ.Stack → Prop
| get  : Γ.tables.list.get x = (l, t)
       → Instr Γ (.get (Vec.index Γ.tables x)) ⟨[i32], [ref t]⟩
| set  : Γ.tables.list.get x = (l, t)
       → Instr Γ (.set (Vec.index Γ.tables x)) ⟨[i32, ref t], []⟩
| size : Γ.tables.list.get x = tt
       → Instr Γ (.size (Vec.index Γ.tables x)) ⟨[], [i32]⟩
| grow : Γ.tables.list.get x = (l, t)
       → Instr Γ (.grow (Vec.index Γ.tables x)) ⟨[ref t, i32], [i32]⟩
| fill : Γ.tables.list.get x = (l, t)
       → Instr Γ (.fill (Vec.index Γ.tables x)) ⟨[i32, ref t, i32], []⟩
| copy : Γ.tables.list.get x = (lim1, t)
       → Γ.tables.list.get y = (lim2, t)
       → Instr Γ (.copy (Vec.index Γ.tables x) (Vec.index Γ.tables y))
          ⟨[i32, i32, i32], []⟩
| init : Γ.tables.list.get x = (lim1, t)
       → Γ.elems.list.get y = t
       → Instr Γ (.init (Vec.index Γ.tables x) (Vec.index Γ.elems y))
          ⟨[i32, i32, i32], []⟩

inductive Memory.Integer.Instr (Γ : Context) : Instr.Memory.Integer nn → Typ.Stack → Prop
| load    : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ nn.toBytes
          → Instr Γ (.load arg) ⟨[i32], [toIntOpd nn]⟩
| store   : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ nn.toBytes
          → Instr Γ (.store arg) ⟨[i32, toIntOpd nn], []⟩
| load8   : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ 1
          → Instr Γ (.load8 s arg) ⟨[i32], [toIntOpd nn]⟩
| load16  : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ 2
          → Instr Γ (.load16 s arg) ⟨[i32], [toIntOpd nn]⟩
| load32  : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ 4
          → Instr Γ (.load32 s arg) ⟨[i32], [toIntOpd nn]⟩
| store8  : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ 1
          → Instr Γ (.store8 s arg) ⟨[i32, toIntOpd nn], []⟩
| store16 : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ 2
          → Instr Γ (.store16 s arg) ⟨[i32, toIntOpd nn], []⟩
| store32 : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ 4
          → Instr Γ (.store32 s arg) ⟨[i32, toIntOpd nn], []⟩

inductive Memory.Float.Instr (Γ : Context) : Instr.Memory.Float nn → Typ.Stack → Prop
| load    : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ nn.toBytes
          → Instr Γ (.load arg) ⟨[i32], [toFloatOpd nn]⟩
| store   : Γ.mems.list.length > 0
          → Nat.pow 2 arg.align.val ≤ nn.toBytes
          → Instr Γ (.store arg) ⟨[i32, toFloatOpd nn], []⟩

inductive Memory.Instr (Γ : Context) : Instr.Memory → Typ.Stack → Prop
| integer   : Memory.Integer.Instr Γ instr type
            → Instr Γ (.integer instr) type
| float     : Memory.Float.Instr Γ instr type
            → Instr Γ (.float instr) type
| size      : Γ.mems.list.length > 0
            → Instr Γ .size ⟨[], [i32]⟩
| grow      : Γ.mems.list.length > 0
            → Instr Γ .grow ⟨[i32], [i32]⟩
| fill      : Γ.mems.list.length > 0
            → Instr Γ .fill ⟨[i32, i32, i32], []⟩
| copy      : Γ.mems.list.length > 0
            → Instr Γ .copy ⟨[i32, i32, i32], []⟩
| init      : Γ.mems.list.length > 0
            → Γ.datas.list.get x = ()
            → Instr Γ (.init (Vec.index Γ.datas x)) ⟨[i32, i32, i32], []⟩
| data_drop : Γ.datas.list.get x = ()
            → Instr Γ (.data_drop (Vec.index Γ.datas x)) ⟨[], []⟩

mutual
inductive Instr : (Γ : Context) → Instr → Typ.Stack → Prop
| numeric       : Numeric.Instr Γ instr type
                → Instr Γ (.numeric instr) type
| reference     : Reference.Instr Γ instr type
                → Instr Γ (.reference instr) type
-- Parametric
| drop          : Instr Γ .drop ⟨[t], []⟩
| select_none   : Instr Γ (.select .none) ⟨[t, t, i32], [t]⟩
| select_num    : Instr Γ (.select (.some [.num t])) ⟨[.val (.num t), .val (.num t), i32], [.val (.num t)]⟩
| select_vec    : Instr Γ (.select (.some [.vec t])) ⟨[.val (.vec t), .val (.vec t), i32], [.val (.vec t)]⟩
| locl          : Local.Instr Γ instr type
                → Instr Γ (.locl instr) type
| globl         : Global.Instr Γ instr type
                → Instr Γ (.globl instr) type
| table         : Table.Instr Γ instr type
                → Instr Γ (.table instr) type
| elem_drop     : Γ.elems.list.get x = t
                → Instr Γ (.elem_drop (Vec.index Γ.elems x)) ⟨[], []⟩
| memory        : Memory.Instr Γ instr type
                → Instr Γ (.memory instr) type
-- Control
| nop           : Instr Γ .nop ⟨[], []⟩
| unreachable   : Instr Γ .unreachable ⟨t1, t2⟩
| block         : {h : List.length Γ.labels.list + 1 < Vec.max_length}
                → Typ.Block Γ blocktype ⟨t1, t2⟩
                → Instrs {Γ with labels := Vec.cons t2 Γ.labels h} instrs ⟨t1.list.map .val, t2.list.map .val⟩
                → Instr Γ (.block blocktype instrs .wasm_end) ⟨t1.list.map .val, t2.list.map .val⟩
| loop          : {h : List.length Γ.labels.list + 1 < Vec.max_length}
                → Typ.Block Γ blocktype ⟨t1, t2⟩
                → Instrs {Γ with labels := Vec.cons t2 Γ.labels h} instrs ⟨t1.list.map .val, t2.list.map .val⟩
                → Instr Γ (.block blocktype instrs .wasm_end) ⟨t1.list.map .val, t2.list.map .val⟩
| wasm_if       : {h : List.length Γ.labels.list + 1 < Vec.max_length}
                → Typ.Block Γ blocktype ⟨t1, t2⟩
                → Instrs {Γ with labels := Vec.cons t2 Γ.labels h} instrs1 ⟨t1.list.map .val, t2.list.map .val⟩
                → Instrs {Γ with labels := Vec.cons t2 Γ.labels h} instrs2 ⟨t1.list.map .val, t2.list.map .val⟩
                → Instr Γ (.wasm_if blocktype instrs1 .wasm_else instrs2 .wasm_end)
                    ⟨t1.list.map .val |>.append [i32], t2.list.map .val⟩
| br            : Γ.labels.list.get l = t
                → Instr Γ (.br (Vec.index Γ.labels l)) ⟨List.append t1 (t.list.map .val), t2⟩
| br_if         : Γ.labels.list.get l = t
                → Instr Γ (.br (Vec.index Γ.labels l)) ⟨(t.list.map .val).append [i32], t2⟩
| br_table_nil  : Typ.MatchList t (Γ.labels.list.get ln |>.list.map .val)
                → Instr Γ (.br_table Vec.nil (Vec.index Γ.labels ln))
                    ⟨List.append t1 t |>.append [i32], t2⟩
| br_table_cons : {h : List.length ls.list + 1 < Vec.max_length}
                → Typ.MatchList t (Γ.labels.list.get l |>.list.map .val)
                → Instr Γ (.br_table ls ln)
                    ⟨List.append t1 t |>.append [i32], t2⟩
                → Instr Γ (.br_table (Vec.cons (Vec.index Γ.labels l) ls h) ln)
                    ⟨List.append t1 t |>.append [i32], t2⟩
| wasm_return   : Γ.labels.list.get l = t
                → Instr Γ (.br (Vec.index Γ.labels l)) ⟨List.append t1 (t.list.map .val), t2⟩
| call          : Γ.funcs.list.get x = ⟨t1, t2⟩
                → Instr Γ (.call (Vec.index Γ.funcs x)) ⟨t1.list.map .val, t2.list.map .val⟩
| call_indirect : Γ.tables.list.get x = ⟨limits, fref⟩
                → Γ.types.list.get y = ⟨t1, t2⟩
                → Instr Γ (.call_indirect (Vec.index Γ.tables x) (Vec.index Γ.types y))
                    ⟨t1.list.map .val |>.append [i32], t2.list.map .val⟩

inductive Instrs : (Γ : Context) → List Instr → Typ.Stack → Prop
| nil  : Instrs Γ [] ⟨t1, t2⟩
| cons : Instrs Γ instrs ⟨t1, List.append t0 t'⟩
       → Typ.MatchList t' t
       → Instr Γ instr ⟨t, t3⟩
       → Instrs Γ (instr :: instrs) ⟨t1, t3⟩
end

inductive Expr : (Γ : Context) → Syntax.Expr → Syntax.Typ.Result → Prop
| expr : Statics.Instrs Γ instrs ⟨[], t'⟩ → Statics.Typ.MatchList t' (t.list.map .val) → Expr Γ (instrs, .wasm_end) t

inductive Instr.Constant : (Γ : Context) → Syntax.Instr → Prop
| const_int   : Constant Γ (.numeric (.integer (.const v)))
| const_float : Constant Γ (.numeric (.float (.const v)))
| ref_null    : Constant Γ (.reference (.null t))
| ref_func    : Constant Γ (.reference (.func t))
| global_get  : Γ.globals.list.get x = (.const, t) → Constant Γ (.globl (.get (Vec.index Γ.globals x)))

inductive Expr.Constant : (Γ : Context) → Syntax.Expr → Prop
| nil  : Constant Γ ([], .wasm_end)
| cons : Constant Γ (instrs, .wasm_end) → Constant Γ (instr :: instrs, .wasm_end)
