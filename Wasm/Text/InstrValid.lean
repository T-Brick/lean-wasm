/- Encoding of defintion WASM's instruction defintion:
    https://webassembly.github.io/spec/core/text/instructions.html
-/


-- TODO WORK IN PROGRESS

import Wasm.Syntax.Instr
import Wasm.Text.Typ
import Wasm.Text.Context
import Wasm.Text.Index

namespace Wasm.Text

open Text.Module

inductive Label : (I : Ident.Context) → Ident.Context → Type
| new
    : (v : Ident)
    → (.some v) ∉ I.labels
    → Label I {I with labels := .some v :: I.labels}
| shadow
    : (v : Ident)
    → I.labels.get i = .some v
    → Label I {I with labels := .some v :: (I.labels.set i.val .none)}
| no_label : Label I {I with labels := .none :: I.labels}

namespace Instr

inductive Reference (I : Ident.Context)
| null : Typ.Heap → Reference I
| is_null
| func : Index.Function I → Reference I
instance : Coe (Syntax.Instr.Reference) (Reference I) :=
  ⟨ fun | .null t  => .null t
        | .is_null => .is_null
        | .func i => .func i
  ⟩

inductive Local (I : Ident.Context)
| get : Index.Local I → Local I
| set : Index.Local I → Local I
| tee : Index.Local I → Local I
instance : Coe (Syntax.Instr.Local) (Local I) :=
  ⟨ fun | .get i => .get i
        | .set i => .set i
        | .tee i => .tee i
  ⟩

inductive Global (I : Ident.Context)
| get : Index.Global I → Global I
| set : Index.Global I → Global I
instance : Coe (Syntax.Instr.Global) (Global I) :=
  ⟨ fun | .get i => .get i
        | .set i => .set i
  ⟩

inductive Table (I : Ident.Context)
| get  : Index.Table I → Table I
| set  : Index.Table I → Table I
| size : Index.Table I → Table I
| grow : Index.Table I → Table I
| fill : Index.Table I → Table I
| copy : Index.Table I → Index.Table I → Table I
| init : Index.Table I → Index.Element I → Table I
instance : Coe (Syntax.Instr.Table) (Table I) :=
  ⟨ fun | .get x    => .get x
        | .set x    => .set x
        | .size x   => .size x
        | .grow x   => .grow x
        | .fill x   => .fill x
        | .copy x y => .copy x y
        | .init x y => .init x y
  ⟩

inductive Memory (I : Ident.Context)
| integer : Syntax.Instr.Memory.Integer nn → Memory I
| float   : Syntax.Instr.Memory.Float nn → Memory I
| size
| grow
| fill
| copy
| init : Index.Data I → Memory I
| data_drop : Index.Data I → Memory I
instance : Coe (Syntax.Instr.Memory) (Memory I) :=
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

inductive Instr.Plain (I : Ident.Context) -- todo use/enforce Ident.Context
| numeric       : (Syntax.Instr.Numeric nn) → Instr.Plain I
| reference     : Instr.Reference I → Instr.Plain I
-- Parametric
| drop
| select        : Option (List Syntax.Typ.Val) → Instr.Plain I
| locl          : Instr.Local I → Instr.Plain I
| globl         : Instr.Global I → Instr.Plain I
| table         : Instr.Table I → Instr.Plain I
| elem_drop     : Index.Element I → Instr.Plain I
| memory        : Instr.Memory I → Instr.Plain I
-- Control
| nop
| unreachable
| br            : Index.Label I → Instr.Plain I
| br_if         : Index.Label I → Instr.Plain I
| br_table      : Vec (Index.Label I) → (Index.Label I) → Instr.Plain I
| wasm_return
| call          : Index.Function I → Instr.Plain I
| call_indirect : Index.Table I → Index.Typ I → Instr.Plain I -- todo enforce I'


inductive Instr.BlockType (I : Ident.Context) : Option Typ.Result → Type
| result : (t : Option Typ.Result) → BlockType I t
| labels : Typeuse I x I' → BlockType I (.some x)

instance : Coe (Syntax.Instr.BlockType) (Instr.BlockType I) :=
  ⟨ fun | .index i => sorry
        | .value .none => .result .none
        | .value (.some v) => .result (.some v)
  ⟩

mutual
inductive Instr.Block : (I : Ident.Context) → Type
| block
    : Label I I'
    → Instr.BlockType I
    → Instr.List I'
    → Option Ident
    → Instr.Block I
| loop
    : Label I I'
    → Instr.BlockType I
    → Instr.List I'
    → Option Ident
    → Instr.Block I
| wasm_if
    : Label I I'
    → Instr.BlockType I
    → (if_body : Instr.List I')
    → (id₁ : Option Ident)
    → (else_body : Instr.List I')
    → (id₂ : Option Ident)
    → Instr.Block I

inductive Instr : (I : Ident.Context) → Type
| plain : Instr.Plain I → Instr I
| block : Instr.Block I → Instr I

inductive Instr.List : (I : Ident.Context) → Type
| nil  : Instr.List I
| cons : Instr I → Instr.List I → Instr.List I
end

mutual
def Instr.ofSyntaxInstr : Syntax.Instr → Instr I
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
  | .block bt is _        => .block (.block .no_label bt is .none)
  | .loop bt is _         => sorry
  | .wasm_if bt ib _ ie _ => sorry
  | .br l                 => .plain (.br l)
  | .br_if l              => .plain (.br_if l)
  | .br_table t l         => .plain (.br_table t l)
  | .wasm_return          => .plain (.wasm_return)
  | .call f               => .plain (.call f)
  | .call_indirect f t    => .plain (.call_indirect f t)

end

-- instance : Coe Syntax.Instr (Instr I) :=
  -- ⟨ 
  -- ⟩

end Wasm.Text

def Wasm.Syntax.Typ.BlockType.toString : Wasm.Syntax.Instr.BlockType → String
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
