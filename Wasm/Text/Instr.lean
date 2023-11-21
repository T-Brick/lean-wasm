/- Encoding of defintion WASM's instruction defintion:
    https://webassembly.github.io/spec/core/text/instructions.html
-/
import Wasm.Syntax.Instr
import Wasm.Text.Typ

def Wasm.Syntax.Typ.BlockType.toString : Wasm.Syntax.Typ.BlockType → String
  | .value .none     => ""
  | .value (.some x) => x.toString
  | .index i => sorry

namespace Wasm.Syntax.Instr

namespace Numeric

def Size.toString : Size → String
  | .double => "32"
  | .quad   => "64"
instance : ToString Size := ⟨Size.toString⟩

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
