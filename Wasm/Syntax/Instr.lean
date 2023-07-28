/- Encoding of defintion WASM's instruction defintion:
    https://webassembly.github.io/spec/core/syntax/instructions.html
-/
import Wasm.Util
import Wasm.Syntax.Opcode
import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Syntax.Index

inductive Wasm.Syntax.Typ.BlockType
| index : Module.Index.Typ → BlockType
| value : Option Typ.Val → BlockType

def Wasm.Syntax.Typ.BlockType.toString : Wasm.Syntax.Typ.BlockType → String
  | .value .none     => ""
  | .value (.some x) => x.toString
  | .index i => sorry

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

def Size.toString : Size → String
  | .double => "32"
  | .quad   => "64"
instance : ToString Size := ⟨Size.toString⟩

inductive Sign
| u | s

inductive Integer.Unop
| clz | ctz | popcnt

inductive Integer.Binop
| add
| sub
| mul
| div : Sign → Integer.Binop
| mod : Sign → Integer.Binop
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
| const         : (v : Value.Unsigned nn.toBits) → Integer nn
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
  offset : Value.Unsigned32
  align  : Value.Unsigned32

inductive Integer : (nn : Numeric.Size) → Type
| load    : Arg → Integer nn
| store   : Arg → Integer nn
| load8   : Numeric.Sign → Arg → Integer nn
| load16  : Numeric.Sign → Arg → Integer nn
| load32  : Numeric.Sign → Arg → Integer .quad
| store8  : Numeric.Sign → Arg → Integer nn
| store16 : Numeric.Sign → Arg → Integer nn
| store32 : Numeric.Sign → Arg → Integer .quad


inductive Float : (nn : Numeric.Size) → Type
| load   : Arg → Float nn
| store  : Arg → Float nn

-- todo: do vectors

end Memory

inductive Memory
| integer : Memory.Integer nn → Memory
| float   : Memory.Float nn → Memory
| size
| grow
| fill
| copy
| init : Module.Index.Data → Memory
| data_drop : Module.Index.Data → Memory



end Instr

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
| block         : Typ.BlockType → List Instr → (wasm_end : Instr.Pseudo) → Instr
| loop          : Typ.BlockType → List Instr → (wasm_end : Instr.Pseudo) → Instr
| wasm_if       : Typ.BlockType → List Instr → (wasm_else : Instr.Pseudo)
                → List Instr → (wasm_end : Instr.Pseudo) → Instr
| br            : Module.Index.Label → Instr
| br_if         : Module.Index.Label → Instr
| br_table      : (Vec Module.Index.Label) → Module.Index.Label → Instr
| wasm_return
| call          : Module.Index.Function → Instr
| call_indirect : Module.Index.Table → Module.Index.Typ → Instr

def Expr := List Instr × Instr.Pseudo

namespace Instr.Numeric

def Sign.toString : Sign → String
  | .s => "s"
  | .u => "u"
instance : ToString Sign := ⟨Sign.toString⟩

namespace Integer

def Unop.toString : Unop → String
  | .clz    => "clz"
  | .ctz    => "ctz"
  | .popcnt => "popcnt"
instance : ToString Unop := ⟨Unop.toString⟩

def Binop.toString : Binop → String
  | .add   => "add"
  | .sub   => "sub"
  | .mul   => "mul"
  | .div s => s!"div_{s}"
  | .mod s => s!"mod_{s}"
  | .and   => "and"
  | .or    => "or"
  | .xor   => "xor"
  | .shl   => "shl"
  | .shr s => s!"shr_{s}"
  | .rotl  => "rotl"
  | .rotr  => "rotr"
instance : ToString Binop := ⟨Binop.toString⟩

def Test.toString : Test → String
  | .eqz => "eqz"
instance : ToString Test := ⟨Test.toString⟩

def Relation.toString : Relation → String
  | .eq   => "eq"
  | .ne   => "ne"
  | .lt s => s!"lt_{s}"
  | .gt s => s!"gt_{s}"
  | .le s => s!"le_{s}"
  | .ge s => s!"ge_{s}"
instance : ToString Relation := ⟨Relation.toString⟩

def toString : Integer nn → String
  | .const v          => s!"i{nn}.const {v}"
  | .unop op          => s!"i{nn}.{op}"
  | .binop op         => s!"i{nn}.{op}"
  | .test op          => s!"i{nn}.{op}"
  | .relation op      => s!"i{nn}.{op}"
  | .extend8_s        => s!"i{nn}.extend8_s"
  | .extend16_s       => s!"i{nn}.extend16_s"
  | .extend32_s       => s!"i{nn}.extend32_s"
  | .wrap_i64         => s!"i{nn}.wrap_i64"
  | .extend_i32 s     => s!"i{nn}.extend_i32_{s}"
  | .trunc_f mm s     => s!"i{nn}.trunc_f{mm}_{s}"
  | .trunc_sat_f mm s => s!"i{nn}.trunc_sat_f{mm}_{s}"
  | .reinterpret_f    => s!"i{nn}.reinterpret_f{nn}"
instance : ToString (Integer nn) := ⟨toString⟩

end Integer

namespace Float

def Unop.toString : Unop → String
  | .abs     => "abs"
  | .neg     => "neg"
  | .sqrt    => "sqrt"
  | .ceil    => "ceil"
  | .floor   => "floor"
  | .trunc   => "trunc"
  | .nearest => "nearest"
instance : ToString Unop := ⟨Unop.toString⟩

def Binop.toString : Binop → String
  | .add      => "add"
  | .sub      => "sub"
  | .mul      => "mul"
  | .div      => "div"
  | .min      => "min"
  | .max      => "max"
  | .copysign => "copysign"
instance : ToString Binop := ⟨Binop.toString⟩

def Relation.toString : Relation → String
  | .eq => "eq"
  | .ne => "ne"
  | .lt => "lt"
  | .gt => "gt"
  | .le => "le"
  | .ge => "ge"
instance : ToString Relation := ⟨Relation.toString⟩

def toString : Float (nn : Numeric.Size) → String
  | .const v        => s!"f{nn}.const v"
  | .unop op        => s!"f{nn}.{op}"
  | .binop op       => s!"f{nn}.{op}"
  | .relation op    => s!"f{nn}.{op}"
  | .demote_f64     => s!"f{nn}.demote_f64"
  | .promote_f32    => s!"f{nn}.promote_f32"
  | .convert_i mm s => s!"f{nn}.convert_i{mm}_{s}"
  | .reinterpret_i  => s!"f{nn}.reinterpret_i{nn}"
instance : ToString (Float nn) := ⟨Float.toString⟩

end Float

def toString : Numeric nn → String
  | .integer i => i.toString
  | .float   f => f.toString
instance : ToString (Numeric nn) := ⟨Numeric.toString⟩

end Numeric

def Reference.toString : Reference → String
  | .null ty  => s!"ref.null {ty}"
  | .is_null  => "ref.is_null"
  | .func idx => s!"ref.func {idx}"
instance : ToString Reference := ⟨Reference.toString⟩

def Local.toString : Local → String
  | .get x => s!"local.get {x}"
  | .set x => s!"local.set {x}"
  | .tee x => s!"local.tee {x}"
instance : ToString Local := ⟨Local.toString⟩


def Global.toString : Global → String
  | .get x => s!"global.get {x}"
  | .set x => s!"global.set {x}"
instance : ToString Global := ⟨Global.toString⟩

def Table.toString : Table → String
  | .get x    => s!"table.get {x}"
  | .set x    => s!"table.set {x}"
  | .size x   => s!"table.size {x}"
  | .grow x   => s!"table.grow {x}"
  | .fill x   => s!"table.fill {x}"
  | .copy x y => s!"table.copy {x} {y}"
  | .init x y => s!"table.init {x} {y}"
instance : ToString Table := ⟨Table.toString⟩

namespace Memory

def Arg.toString (a : Arg) : String :=
  s!"offset={a.offset} align={a.align}"
instance : ToString Arg := ⟨Arg.toString⟩

def Integer.toString : Integer nn → String
  | .load m      => s!"i{nn}.load {m}"
  | .store m     => s!"i{nn}.store {m}"
  | .load8 s m   => s!"i{nn}.load8_{s} {m}"
  | .load16 s m  => s!"i{nn}.load16_{s} {m}"
  | .load32 s m  => s!"i{nn}.load32_{s} {m}"
  | .store8 s m  => s!"i{nn}.store8_{s} {m}"
  | .store16 s m => s!"i{nn}.store16_{s} {m}"
  | .store32 s m => s!"i{nn}.store32_{s} {m}"
instance : ToString (Integer nn) := ⟨Integer.toString⟩


def Float.toString : Float nn → String
  | load m  => s!"f{nn}.load {m}"
  | store m => s!"f{nn}.store {m}"
instance : ToString (Float nn) := ⟨Float.toString⟩

def toString : Memory → String
  | .integer i   => i.toString
  | .float f     => f.toString
  | .size        => "memory.size"
  | .grow        => "memory.grow"
  | .fill        => "memory.fill"
  | .copy        => "memory.copy"
  | .init x      => s!"memory.init {x}"
  | .data_drop x => s!"data.drop {x}"
instance : ToString Memory := ⟨toString⟩

end Memory


def Pseudo.toString : Pseudo → String
  | .wasm_end   => "end"
  | .wasm_else  => "else"
instance : ToString Pseudo := ⟨Pseudo.toString⟩

def toString : Instr → String
  | .numeric      n => s!"({n})"
  | .reference    r => s!"({r})"
  -- Parametric
  | .drop           => "drop"
  | .select s       => sorry
  | .locl l         => s!"({l})"
  | .globl g        => s!"({g})"
  | .table t        => s!"({t})"
  | .elem_drop x    => s!"(elem.drop {x})"
  | .memory m       => s!"({m})"
  -- Control
  | .nop            => "nop"
  | .unreachable    => "unreachable"
  | .block bt ins e => sorry
  | .loop  bt ins e => sorry
  | .wasm_if bt ins el ins' e => sorry
  | .br l           => s!"(br {l})"
  | .br_if l        => s!"(br_if {l})"
  | .br_table ls l  => s!"(br_table {ls} {l})"
  | .wasm_return    => "return"
  | .call x         => s!"(call {x})"
  | .call_indirect t typ => sorry
