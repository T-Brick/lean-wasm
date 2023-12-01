/- Encoding of defintion WASM's instruction defintion:
    https://webassembly.github.io/spec/core/syntax/instructions.html
-/
import Wasm.Vec
import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Syntax.Index
import Numbers
open Numbers

namespace Wasm.Syntax.Instr

namespace Numeric

inductive Size
| double | quad -- 32/64

def Size.toBits : Size → {i : Nat // i > 0}
  | double => ⟨32, by simp⟩
  | quad   => ⟨64, by simp⟩

def Size.max_double : Nat := Nat.pow 2 (Size.toBits .double)
def Size.max_quad   : Nat := Nat.pow 2 (Size.toBits .quad)
def Size.max_val : Size → Nat
  | double => Size.max_double
  | quad   => Size.max_quad

theorem Size.max_val_gt_zero : Size.max_val n > 0 := by
  cases n with
  | double => simp
  | quad   => simp

def Size.toBytes : Size → Nat
  | double => 4
  | quad   => 8

def Size.toIntVal : Size → Typ.Val
  | .double => .num .i32
  | .quad   => .num .i64

def Size.toFloatVal : Size → Typ.Val
  | .double => .num .f32
  | .quad   => .num .f64

inductive Sign
| u | s

inductive Integer.Unop
| clz | ctz | popcnt

inductive Integer.Binop
| add
| sub
| mul
| div : Sign → Integer.Binop
| rem : Sign → Integer.Binop
| and
| or
| xor
| shl
| shr : Sign → Integer.Binop
| rotl
| rotr

inductive Integer.Test
| eqz

inductive Integer.Relation
| eq
| ne
| lt : Sign → Integer.Relation
| gt : Sign → Integer.Relation
| le : Sign → Integer.Relation
| ge : Sign → Integer.Relation

inductive Integer : (nn : Numeric.Size) → Type
| const         : (v : Unsigned nn.toBits) → Integer nn
| unop          : Integer.Unop → Integer nn
| binop         : Integer.Binop → Integer nn
| test          : Integer.Test → Integer nn
| relation      : Integer.Relation → Integer nn
| extend8_s     : Integer nn
| extend16_s    : Integer nn
| extend32_s    : Integer .quad
| wrap_i64      : Integer .double
| extend_i32    : Sign → Integer .quad
| trunc_f       : (mm : Size) → Sign → Integer nn
| trunc_sat_f   : (mm : Size) → Sign → Integer nn
| reinterpret_f : Integer nn

inductive Float.Unop
| abs
| neg
| sqrt
| ceil
| floor
| trunc
| nearest

inductive Float.Binop
| add
| sub
| mul
| div
| min
| max
| copysign

inductive Float.Relation
| eq
| ne
| lt
| gt
| le
| ge

inductive Float : (nn : Numeric.Size) → Type
| const         : (v : Value.FloatN nn.toBits) → Float nn
| unop          : Float.Unop → Float nn
| binop         : Float.Binop → Float nn
| relation      : Float.Relation → Float nn
| demote_f64    : Float .double
| promote_f32   : Float .quad
| convert_i     : (mm : Size) → Sign → Float nn
| reinterpret_i : Float nn

end Numeric

inductive Numeric : (nn : Numeric.Size) → Type
| integer : Numeric.Integer nn → Numeric nn
| float   : Numeric.Float nn → Numeric nn



-- todo vector instructions

inductive Reference
| null : Typ.Ref → Reference
| is_null
| func : Module.Index.Function → Reference

inductive Local
| get : Module.Index.Local → Local
| set : Module.Index.Local → Local
| tee : Module.Index.Local → Local

inductive Global
| get : Module.Index.Global → Global
| set : Module.Index.Global → Global

inductive Table
| get  : Module.Index.Table → Table
| set  : Module.Index.Table → Table
| size : Module.Index.Table → Table
| grow : Module.Index.Table → Table
| fill : Module.Index.Table → Table
| copy : Module.Index.Table → Module.Index.Table → Table
| init : Module.Index.Table → Module.Index.Element → Table

namespace Memory

structure Arg where
  offset : Unsigned32
  align  : Unsigned32

inductive Integer : (nn : Numeric.Size) → Type
| load    : Arg → Integer nn
| store   : Arg → Integer nn
| load8   : Numeric.Sign → Arg → Integer nn
| load16  : Numeric.Sign → Arg → Integer nn
| load32  : Numeric.Sign → Arg → Integer .quad
| store8  : Arg → Integer nn
| store16 : Arg → Integer nn
| store32 : Arg → Integer .quad


inductive Float : (nn : Numeric.Size) → Type
| load   : Arg → Float nn
| store  : Arg → Float nn

-- todo: do vectors

end Memory

inductive Memory
| integer   : Memory.Integer nn → Memory
| float     : Memory.Float nn → Memory
| size
| grow
| fill
| copy
| init      : Module.Index.Data → Memory
| data_drop : Module.Index.Data → Memory



end Instr

inductive Instr.BlockType
| index : Module.Index.Typ → BlockType
| value : Option Typ.Val → BlockType

inductive Instr.Pseudo
| wasm_end
| wasm_else

inductive Instr : Type
| numeric       : (Instr.Numeric nn) → Instr
| reference     : Instr.Reference → Instr
-- Parametric
| drop
| select        : Option (List Typ.Val) → Instr
| locl          : Instr.Local → Instr
| globl         : Instr.Global → Instr
| table         : Instr.Table → Instr
| elem_drop     : Module.Index.Element → Instr
| memory        : Instr.Memory → Instr
-- Control
| nop
| unreachable
| block         : Instr.BlockType → List Instr → (wasm_end : Instr.Pseudo) → Instr
| loop          : Instr.BlockType → List Instr → (wasm_end : Instr.Pseudo) → Instr
| wasm_if       : Instr.BlockType → List Instr → (wasm_else : Instr.Pseudo)
                → List Instr → (wasm_end : Instr.Pseudo) → Instr
| br            : Module.Index.Label → Instr
| br_if         : Module.Index.Label → Instr
| br_table      : (Vec Module.Index.Label) → Module.Index.Label → Instr
| wasm_return
| call          : Module.Index.Function → Instr
| call_indirect : Module.Index.Table → Module.Index.Typ → Instr

def Expr := List Instr × Instr.Pseudo
