/- Encoding of defintion WASM's instruction defintion:
    https://webassembly.github.io/spec/core/text/instructions.html
-/

import Wasm.Syntax.Instr
import Wasm.Text.Typ
import Wasm.Text.Context
import Wasm.Text.Index

namespace Wasm.Text

open Text.Module

inductive Label
| name : Ident → Label
| no_label

namespace Instr

inductive Reference
| null : Typ.Heap → Reference
| is_null
| func : Index.Function → Reference
instance : Coe Syntax.Instr.Reference Reference :=
  ⟨ fun | .null t  => .null t
        | .is_null => .is_null
        | .func i  => .func i
  ⟩

inductive Local
| get : Index.Local → Local
| set : Index.Local → Local
| tee : Index.Local → Local
instance : Coe Syntax.Instr.Local Local :=
  ⟨ fun | .get i => .get i
        | .set i => .set i
        | .tee i => .tee i
  ⟩

inductive Global
| get : Index.Global → Global
| set : Index.Global → Global
instance : Coe Syntax.Instr.Global Global :=
  ⟨ fun | .get i => .get i
        | .set i => .set i
  ⟩

inductive Table
| get  : Index.Table → Table
| set  : Index.Table → Table
| size : Index.Table → Table
| grow : Index.Table → Table
| fill : Index.Table → Table
| copy : Index.Table → Index.Table → Table
| init : Index.Table → Index.Element → Table
instance : Coe Syntax.Instr.Table Table :=
  ⟨ fun | .get x    => .get x
        | .set x    => .set x
        | .size x   => .size x
        | .grow x   => .grow x
        | .fill x   => .fill x
        | .copy x y => .copy x y
        | .init x y => .init x y
  ⟩

inductive Memory
| integer : Syntax.Instr.Memory.Integer nn → Memory
| float   : Syntax.Instr.Memory.Float nn → Memory
| size
| grow
| fill
| copy
| init : Index.Data → Memory
| data_drop : Index.Data → Memory
instance : Coe Syntax.Instr.Memory Memory :=
  ⟨ fun | .integer i   => .integer i
        | .float f     => .float f
        | .size        => .size
        | .grow        => .grow
        | .fill        => .fill
        | .copy        => .copy
        | .init x      => .init x
        | .data_drop x => .data_drop x
  ⟩

end Instr

inductive Instr.Plain
| numeric       : (Syntax.Instr.Numeric nn) → Instr.Plain
| reference     : Instr.Reference → Instr.Plain
-- Parametric
| drop
| select        : Option (List Syntax.Typ.Val) → Instr.Plain
| locl          : Instr.Local → Instr.Plain
| globl         : Instr.Global → Instr.Plain
| table         : Instr.Table → Instr.Plain
| elem_drop     : Index.Element → Instr.Plain
| memory        : Instr.Memory → Instr.Plain
-- Control
| nop
| unreachable
| br            : Index.Label → Instr.Plain
| br_if         : Index.Label → Instr.Plain
| br_table      : Vec Index.Label → Index.Label → Instr.Plain
| wasm_return
| call          : Index.Function → Instr.Plain
| call_indirect : Index.Table → Index.Typ → Instr.Plain


inductive Instr.BlockType
| value : (t : Option Typ.Result) → BlockType
| index : Index.Typ → BlockType

instance : Coe (Syntax.Instr.BlockType) Instr.BlockType :=
  ⟨ fun | .index i => .index i
        | .value .none => .value .none
        | .value (.some v) => .value (.some v)
  ⟩

mutual
inductive Instr.Block
| block : Label → Instr.BlockType → List Instr → Option Ident → Instr.Block
| loop  : Label → Instr.BlockType → List Instr → Option Ident → Instr.Block
| wasm_if
    : Label
    → Instr.BlockType
    → (if_body : List Instr)
    → (id₁ : Option Ident)
    → (else_body : List Instr)
    → (id₂ : Option Ident)
    → Instr.Block

inductive Instr
| plain : Instr.Plain → Instr
| block : Instr.Block → Instr
| comment : String → Instr
end

mutual
def Instr.ofSyntaxInstr : Syntax.Instr → Instr
  | .numeric n            => .plain (.numeric n)
  | .reference r          => .plain (.reference r)
  | .drop                 => .plain .drop
  | .select v             => .plain (.select v)
  | .locl l               => .plain (.locl l)
  | .globl g              => .plain (.globl g)
  | .table t              => .plain (.table t)
  | .elem_drop e          => .plain (.elem_drop e)
  | .memory m             => .plain (.memory m)
  | .nop                  => .plain .nop
  | .unreachable          => .plain .unreachable
  | .block bt is _        =>
    .block (.block .no_label bt (Instr.ofSyntaxInstrList is) .none)
  | .loop bt is _         =>
    .block (.loop .no_label bt (Instr.ofSyntaxInstrList is) .none)
  | .wasm_if bt ib _ ie _ => .block (
      .wasm_if .no_label bt (Instr.ofSyntaxInstrList ib) .none
                            (Instr.ofSyntaxInstrList ie) .none
    )
  | .br l                 => .plain (.br l)
  | .br_if l              => .plain (.br_if l)
  | .br_table t l         => .plain (.br_table t l)
  | .wasm_return          => .plain (.wasm_return)
  | .call f               => .plain (.call f)
  | .call_indirect f t    => .plain (.call_indirect f t)

def Instr.ofSyntaxInstrList : List Syntax.Instr → List Instr
  | [] => []
  | i :: is => Instr.ofSyntaxInstr i :: ofSyntaxInstrList is

end
termination_by
  Instr.ofSyntaxInstr i => sizeOf i
  Instr.ofSyntaxInstrList is => sizeOf is

instance : Coe Syntax.Instr Instr := ⟨Instr.ofSyntaxInstr⟩


nonrec def Label.toString : Label → String
  | .name n => toString n
  | .no_label => ""
instance : ToString Label := ⟨Label.toString⟩

namespace Instr

namespace Numeric

def Size.toString : Syntax.Instr.Numeric.Size → String
  | .double => "32"
  | .quad   => "64"
instance : ToString Syntax.Instr.Numeric.Size := ⟨Size.toString⟩

def Sign.toString : Syntax.Instr.Numeric.Sign → String
  | .s => "s"
  | .u => "u"
instance : ToString Syntax.Instr.Numeric.Sign := ⟨Sign.toString⟩

namespace Integer

def Unop.toString : Syntax.Instr.Numeric.Integer.Unop → String
  | .clz    => "clz"
  | .ctz    => "ctz"
  | .popcnt => "popcnt"
instance : ToString Syntax.Instr.Numeric.Integer.Unop := ⟨Unop.toString⟩

def Binop.toString : Syntax.Instr.Numeric.Integer.Binop → String
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
instance : ToString Syntax.Instr.Numeric.Integer.Binop := ⟨Binop.toString⟩

def Test.toString : Syntax.Instr.Numeric.Integer.Test → String
  | .eqz => "eqz"
instance : ToString Syntax.Instr.Numeric.Integer.Test := ⟨Test.toString⟩

def Relation.toString : Syntax.Instr.Numeric.Integer.Relation → String
  | .eq   => "eq"
  | .ne   => "ne"
  | .lt s => s!"lt_{s}"
  | .gt s => s!"gt_{s}"
  | .le s => s!"le_{s}"
  | .ge s => s!"ge_{s}"
instance : ToString Syntax.Instr.Numeric.Integer.Relation := ⟨Relation.toString⟩

def toString : Syntax.Instr.Numeric.Integer nn → String
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
instance : ToString (Syntax.Instr.Numeric.Integer nn) := ⟨toString⟩

end Integer

namespace Float

def Unop.toString : Syntax.Instr.Numeric.Float.Unop → String
  | .abs     => "abs"
  | .neg     => "neg"
  | .sqrt    => "sqrt"
  | .ceil    => "ceil"
  | .floor   => "floor"
  | .trunc   => "trunc"
  | .nearest => "nearest"
instance : ToString Syntax.Instr.Numeric.Float.Unop := ⟨Unop.toString⟩

def Binop.toString : Syntax.Instr.Numeric.Float.Binop → String
  | .add      => "add"
  | .sub      => "sub"
  | .mul      => "mul"
  | .div      => "div"
  | .min      => "min"
  | .max      => "max"
  | .copysign => "copysign"
instance : ToString Syntax.Instr.Numeric.Float.Binop := ⟨Binop.toString⟩

def Relation.toString : Syntax.Instr.Numeric.Float.Relation → String
  | .eq => "eq"
  | .ne => "ne"
  | .lt => "lt"
  | .gt => "gt"
  | .le => "le"
  | .ge => "ge"
instance : ToString Syntax.Instr.Numeric.Float.Relation := ⟨Relation.toString⟩

def toString : Syntax.Instr.Numeric.Float (nn : Syntax.Instr.Numeric.Size)
             → String
  | .const v        => s!"f{nn}.const v"
  | .unop op        => s!"f{nn}.{op}"
  | .binop op       => s!"f{nn}.{op}"
  | .relation op    => s!"f{nn}.{op}"
  | .demote_f64     => s!"f{nn}.demote_f64"
  | .promote_f32    => s!"f{nn}.promote_f32"
  | .convert_i mm s => s!"f{nn}.convert_i{mm}_{s}"
  | .reinterpret_i  => s!"f{nn}.reinterpret_i{nn}"
instance : ToString (Syntax.Instr.Numeric.Float nn) := ⟨Float.toString⟩

end Float

nonrec def toString : Syntax.Instr.Numeric nn → String
  | .integer i => toString i
  | .float   f => toString f
instance : ToString (Syntax.Instr.Numeric nn) := ⟨Numeric.toString⟩

end Numeric

def Reference.toString : Reference → String
  | .null ty  => s!"ref.null {ty}"
  | .is_null  => "ref.is_null"
  | .func idx => s!"ref.func {idx}"
instance : ToString Reference := ⟨Reference.toString⟩
instance : ToString Syntax.Instr.Reference := ⟨(Reference.toString ·)⟩

def Local.toString : Local → String
  | .get x => s!"local.get {x}"
  | .set x => s!"local.set {x}"
  | .tee x => s!"local.tee {x}"
instance : ToString Local := ⟨Local.toString⟩
instance : ToString Syntax.Instr.Local := ⟨(Local.toString ·)⟩


def Global.toString : Global → String
  | .get x => s!"global.get {x}"
  | .set x => s!"global.set {x}"
instance : ToString Global := ⟨Global.toString⟩
instance : ToString Syntax.Instr.Global := ⟨(Global.toString ·)⟩

def Table.toString : Table → String
  | .get x    => s!"table.get {x}"
  | .set x    => s!"table.set {x}"
  | .size x   => s!"table.size {x}"
  | .grow x   => s!"table.grow {x}"
  | .fill x   => s!"table.fill {x}"
  | .copy x y => s!"table.copy {x} {y}"
  | .init x y => s!"table.init {x} {y}"
instance : ToString Table := ⟨Table.toString⟩
instance : ToString Syntax.Instr.Table := ⟨(Table.toString ·)⟩

namespace Memory

def Arg.toString (a : Syntax.Instr.Memory.Arg) : String :=
  s!"offset={a.offset} align={a.align}"
instance : ToString Syntax.Instr.Memory.Arg := ⟨Arg.toString⟩

def Integer.toString : Syntax.Instr.Memory.Integer nn → String
  | .load m      => s!"i{nn}.load {m}"
  | .store m     => s!"i{nn}.store {m}"
  | .load8 s m   => s!"i{nn}.load8_{s} {m}"
  | .load16 s m  => s!"i{nn}.load16_{s} {m}"
  | .load32 s m  => s!"i{nn}.load32_{s} {m}"
  | .store8 s m  => s!"i{nn}.store8_{s} {m}"
  | .store16 s m => s!"i{nn}.store16_{s} {m}"
  | .store32 s m => s!"i{nn}.store32_{s} {m}"
instance : ToString (Syntax.Instr.Memory.Integer nn) := ⟨Integer.toString⟩


def Float.toString : Syntax.Instr.Memory.Float nn → String
  | .load m  => s!"f{nn}.load {m}"
  | .store m => s!"f{nn}.store {m}"
instance : ToString (Syntax.Instr.Memory.Float nn) := ⟨Float.toString⟩

nonrec def toString : Memory → String
  | .integer i   => toString i
  | .float f     => toString f
  | .size        => "memory.size"
  | .grow        => "memory.grow"
  | .fill        => "memory.fill"
  | .copy        => "memory.copy"
  | .init x      => s!"memory.init {x}"
  | .data_drop x => s!"data.drop {x}"
instance : ToString Memory := ⟨toString⟩
instance : ToString Syntax.Instr.Memory := ⟨(toString ·)⟩

end Memory

def Plain.toString : Instr.Plain → String
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
  | .br l           => s!"(br {l})"
  | .br_if l        => s!"(br_if {l})"
  | .br_table ls l  => s!"(br_table {ls} {l})"
  | .wasm_return    => "return"
  | .call x         => s!"(call {x})"
  | .call_indirect t typ => sorry
instance : ToString Instr.Plain := ⟨Plain.toString⟩

def BlockType.toString : BlockType → String
  | .value .none     => ""
  | .value (.some x) => x.toString
  | .index i => s!"(type {i})"
instance : ToString BlockType := ⟨BlockType.toString⟩

mutual

def Block.toString : Instr.Block → String
  | .block lbl bt ins id =>
    let ins := listToString ins |>.replace "\n" "\n  "
    s!"(block {lbl} {bt}\n  {ins}\n)"
  | .loop lbl bt ins e =>
    let ins := listToString ins |>.replace "\n" "\n  "
    s!"(loop {lbl} {bt}\n  {ins}\n)"
  | .wasm_if lbl bt ins el ins' e =>
    let ins := listToString ins |>.replace "\n" "\n    "
    let ins' := listToString ins' |>.replace "\n" "\n    "
    s!"(if {lbl} {bt}\n  (then\n    {ins}\n  ) (else\n    {ins'}\n  )\n)"

def toString : Instr → String
  | .plain i   => Plain.toString i
  | .block i   => Block.toString i
  | .comment s => s!"(; {s} ;)"

def listToString : List Instr → String
  | [] => ""
  | i :: is => (toString i) ++ "\n" ++ listToString is

end
termination_by
  Block.toString i => sizeOf i
  Instr.toString i => sizeOf i
  Instr.listToString is => sizeOf is

instance : ToString Instr.Block         := ⟨Instr.Block.toString⟩
instance : ToString Instr               := ⟨Instr.toString⟩
instance : ToString Syntax.Instr        := ⟨(Instr.toString ·)⟩
instance : ToString (List Instr)        := ⟨Instr.listToString⟩
instance : ToString (List Syntax.Instr) := ⟨(Instr.listToString ·)⟩

end Wasm.Text.Instr

namespace Wasm.Syntax.Instr

def Pseudo.toString : Pseudo → String
  | .wasm_end   => "end"
  | .wasm_else  => "else"
instance : ToString Pseudo := ⟨Pseudo.toString⟩

def Expr.toString : Expr → String := (Text.Instr.listToString ·.fst)
instance : ToString Expr := ⟨Expr.toString⟩
