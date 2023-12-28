import Wasm.Text.Notation.Value
import Wasm.Text.Notation.Typ
import Wasm.Text.Notation.Index
import Wasm.Text.Instr

namespace Wasm.Text.Notation

open Numbers Wasm.Text Wasm.Text.Instr

/- Labels -/
declare_syntax_cat wat_label
scoped syntax wat_ident ?  : wat_label
scoped syntax "↑" term:max : wat_label

scoped syntax "[wat_label|" wat_label "]" : term

macro_rules
| `([wat_label| $v:wat_ident ]) => `(Label.name [wat_ident| $v])
| `([wat_label| ])              => `(Label.no_label)
| `([wat_label| ↑$e])           => `($e)

/- Memory Args -/
declare_syntax_cat wat_offset
declare_syntax_cat wat_align
declare_syntax_cat wat_memarg₁  -- todo is there a better way (probably)
declare_syntax_cat wat_memarg₂
declare_syntax_cat wat_memarg₄
declare_syntax_cat wat_memarg₈
scoped syntax ("offset="wat_u32)       : wat_offset
scoped syntax ("align="wat_u32)        : wat_align
scoped syntax wat_offset ? wat_align ? : wat_memarg₁
scoped syntax wat_offset ? wat_align ? : wat_memarg₂
scoped syntax wat_offset ? wat_align ? : wat_memarg₄
scoped syntax wat_offset ? wat_align ? : wat_memarg₈

scoped syntax "[wat_offset|" wat_offset ? "]" : term
scoped syntax "[wat_align₁|" wat_align ? "]"   : term
scoped syntax "[wat_align₂|" wat_align ? "]"   : term
scoped syntax "[wat_align₄|" wat_align ? "]"   : term
scoped syntax "[wat_align₈|" wat_align ? "]"   : term
scoped syntax "[wat_memarg₁|" wat_memarg₁ "]" : term
scoped syntax "[wat_memarg₂|" wat_memarg₂ "]" : term
scoped syntax "[wat_memarg₄|" wat_memarg₄ "]" : term
scoped syntax "[wat_memarg₈|" wat_memarg₈ "]" : term

macro_rules
| `([wat_offset| ]) => `([wat_u32| 0])
| `([wat_offset| offset=$o:wat_u32]) => `([wat_u32| $o])

macro_rules
| `([wat_align₁| align=$a:wat_u32]) =>
    `(Unsigned.ofNat (n:=⟨32, by simp⟩) (Nat.log 2 [wat_u32| $a].toNat))
| `([wat_align₁| ]) => `([wat_u32| 0])
| `([wat_align₂| align=$a:wat_u32]) =>
    `(Unsigned.ofNat (n:=⟨32, by simp⟩) (Nat.log 2 [wat_u32| $a].toNat))
| `([wat_align₂| ]) => `([wat_u32| 1])
| `([wat_align₄| align=$a:wat_u32]) =>
    `(Unsigned.ofNat (n:=⟨32, by simp⟩) (Nat.log 2 [wat_u32| $a].toNat))
| `([wat_align₄| ]) => `([wat_u32| 2])
| `([wat_align₈| align=$a:wat_u32]) =>
    `(Unsigned.ofNat (n:=⟨32, by simp⟩) (Nat.log 2 [wat_u32| $a].toNat))
| `([wat_align₈| ]) => `([wat_u32| 3])

macro_rules
| `([wat_memarg₁| $o:wat_offset $a:wat_align ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| $o] [wat_align₁| $a])
| `([wat_memarg₁| $o:wat_offset ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| $o] [wat_align₁| ])
| `([wat_memarg₁| $a:wat_align ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| ] [wat_align₁| $a])
| `([wat_memarg₁| ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| ] [wat_align₁| ])

| `([wat_memarg₂| $o:wat_offset $a:wat_align ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| $o] [wat_align₂| $a])
| `([wat_memarg₂| $o:wat_offset ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| $o] [wat_align₂| ])
| `([wat_memarg₂| $a:wat_align ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| ] [wat_align₂| $a])
| `([wat_memarg₂| ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| ] [wat_align₂| ])

| `([wat_memarg₄| $o:wat_offset $a:wat_align ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| $o] [wat_align₄| $a])
| `([wat_memarg₄| $o:wat_offset ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| $o] [wat_align₄| ])
| `([wat_memarg₄| $a:wat_align ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| ] [wat_align₄| $a])
| `([wat_memarg₄| ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| ] [wat_align₄| ])

| `([wat_memarg₈| $o:wat_offset $a:wat_align ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| $o] [wat_align₈| $a])
| `([wat_memarg₈| $o:wat_offset ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| $o] [wat_align₈| ])
| `([wat_memarg₈| $a:wat_align ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| ] [wat_align₈| $a])
| `([wat_memarg₈| ]) =>
    `(Syntax.Instr.Memory.Arg.mk [wat_offset| ] [wat_align₈| ])


/- Plain Instructions -/
declare_syntax_cat wat_plaininstr
scoped syntax "unreachable"                              : wat_plaininstr
scoped syntax "nop"                                      : wat_plaininstr
scoped syntax "br" wat_labelidx                          : wat_plaininstr
scoped syntax "br_if" wat_labelidx                       : wat_plaininstr
scoped syntax "br_table" wat_labelidx+                   : wat_plaininstr
scoped syntax "return"                                   : wat_plaininstr
scoped syntax "call" wat_funcidx                         : wat_plaininstr
scoped syntax "call_indirect" wat_tableidx ? wat_typeuse : wat_plaininstr
-- References
scoped syntax "ref.null" wat_heaptype                    : wat_plaininstr
scoped syntax "ref.is_null"                              : wat_plaininstr
scoped syntax "ref.func" wat_funcidx                     : wat_plaininstr
-- Parametric
scoped syntax "drop"                                     : wat_plaininstr
scoped syntax "select" (wat_result*)?                    : wat_plaininstr
-- Variadic
scoped syntax "local.get" wat_localidx                   : wat_plaininstr
scoped syntax "local.set" wat_localidx                   : wat_plaininstr
scoped syntax "local.tee" wat_localidx                   : wat_plaininstr
scoped syntax "global.get" wat_globalidx                 : wat_plaininstr
scoped syntax "global.set" wat_globalidx                 : wat_plaininstr
-- Table
scoped syntax "table.get" wat_tableidx ?                 : wat_plaininstr
scoped syntax "table.set" wat_tableidx ?                 : wat_plaininstr
scoped syntax "table.size" wat_tableidx ?                : wat_plaininstr
scoped syntax "table.grow" wat_tableidx ?                : wat_plaininstr
scoped syntax "table.fill" wat_tableidx ?                : wat_plaininstr
scoped syntax "table.copy" (wat_tableidx wat_tableidx)?  : wat_plaininstr
scoped syntax "table.init" wat_tableidx ? wat_elemidx    : wat_plaininstr
scoped syntax "elem.drop" wat_elemidx                    : wat_plaininstr
-- Memory
scoped syntax "i32.load" wat_memarg₄     : wat_plaininstr
scoped syntax "i64.load" wat_memarg₈     : wat_plaininstr
scoped syntax "f32.load" wat_memarg₄     : wat_plaininstr
scoped syntax "f64.load" wat_memarg₈     : wat_plaininstr
scoped syntax "i32.load8_s" wat_memarg₁  : wat_plaininstr
scoped syntax "i32.load8_u" wat_memarg₁  : wat_plaininstr
scoped syntax "i32.load16_s" wat_memarg₂ : wat_plaininstr
scoped syntax "i32.load16_u" wat_memarg₂ : wat_plaininstr
scoped syntax "i64.load8_s" wat_memarg₁  : wat_plaininstr
scoped syntax "i64.load8_u" wat_memarg₁  : wat_plaininstr
scoped syntax "i64.load16_s" wat_memarg₂ : wat_plaininstr
scoped syntax "i64.load16_u" wat_memarg₂ : wat_plaininstr
scoped syntax "i64.load32_s" wat_memarg₄ : wat_plaininstr
scoped syntax "i64.load32_u" wat_memarg₄ : wat_plaininstr
scoped syntax "i32.store" wat_memarg₄    : wat_plaininstr
scoped syntax "i64.store" wat_memarg₈    : wat_plaininstr
scoped syntax "f32.store" wat_memarg₄    : wat_plaininstr
scoped syntax "f64.store" wat_memarg₈    : wat_plaininstr
scoped syntax "i32.store8" wat_memarg₁   : wat_plaininstr
scoped syntax "i32.store16" wat_memarg₂  : wat_plaininstr
scoped syntax "i64.store8" wat_memarg₁   : wat_plaininstr
scoped syntax "i64.store16" wat_memarg₂  : wat_plaininstr
scoped syntax "i64.store32" wat_memarg₄  : wat_plaininstr
scoped syntax "memory.size"              : wat_plaininstr
scoped syntax "memory.grow"              : wat_plaininstr
scoped syntax "memory.fill"              : wat_plaininstr
scoped syntax "memory.copy"              : wat_plaininstr
scoped syntax "memory.init" wat_dataidx  : wat_plaininstr
scoped syntax "data.drop" wat_dataidx    : wat_plaininstr

-- Numeric (todo floats)
scoped syntax "i32.const" wat_i32 : wat_plaininstr
scoped syntax "i64.const" wat_i64 : wat_plaininstr
-- scoped syntax "f32.const" wat_f32 : wat_plaininstr
-- scoped syntax "f64.const" wat_f64 : wat_plaininstr

scoped syntax "i32.clz"    : wat_plaininstr
scoped syntax "i32.ctz"    : wat_plaininstr
scoped syntax "i32.popcnt" : wat_plaininstr
scoped syntax "i32.add"    : wat_plaininstr
scoped syntax "i32.sub"    : wat_plaininstr
scoped syntax "i32.mul"    : wat_plaininstr
scoped syntax "i32.div_s"  : wat_plaininstr
scoped syntax "i32.div_u"  : wat_plaininstr
scoped syntax "i32.rem_s"  : wat_plaininstr
scoped syntax "i32.rem_u"  : wat_plaininstr
scoped syntax "i32.and"    : wat_plaininstr
scoped syntax "i32.or"     : wat_plaininstr
scoped syntax "i32.xor"    : wat_plaininstr
scoped syntax "i32.shl"    : wat_plaininstr
scoped syntax "i32.shr_s"  : wat_plaininstr
scoped syntax "i32.shr_u"  : wat_plaininstr
scoped syntax "i32.rotl"   : wat_plaininstr
scoped syntax "i32.rotr"   : wat_plaininstr

scoped syntax "i64.clz"    : wat_plaininstr
scoped syntax "i64.ctz"    : wat_plaininstr
scoped syntax "i64.popcnt" : wat_plaininstr
scoped syntax "i64.add"    : wat_plaininstr
scoped syntax "i64.sub"    : wat_plaininstr
scoped syntax "i64.mul"    : wat_plaininstr
scoped syntax "i64.div_s"  : wat_plaininstr
scoped syntax "i64.div_u"  : wat_plaininstr
scoped syntax "i64.rem_s"  : wat_plaininstr
scoped syntax "i64.rem_u"  : wat_plaininstr
scoped syntax "i64.and"    : wat_plaininstr
scoped syntax "i64.or"     : wat_plaininstr
scoped syntax "i64.xor"    : wat_plaininstr
scoped syntax "i64.shl"    : wat_plaininstr
scoped syntax "i64.shr_s"  : wat_plaininstr
scoped syntax "i64.shr_u"  : wat_plaininstr
scoped syntax "i64.rotl"   : wat_plaininstr
scoped syntax "i64.rotr"   : wat_plaininstr

scoped syntax "f32.abs"      : wat_plaininstr
scoped syntax "f32.neg"      : wat_plaininstr
scoped syntax "f32.ceil"     : wat_plaininstr
scoped syntax "f32.floor"    : wat_plaininstr
scoped syntax "f32.trunc"    : wat_plaininstr
scoped syntax "f32.nearest"  : wat_plaininstr
scoped syntax "f32.sqrt"     : wat_plaininstr
scoped syntax "f32.add"      : wat_plaininstr
scoped syntax "f32.sub"      : wat_plaininstr
scoped syntax "f32.mul"      : wat_plaininstr
scoped syntax "f32.div"      : wat_plaininstr
scoped syntax "f32.min"      : wat_plaininstr
scoped syntax "f32.max"      : wat_plaininstr
scoped syntax "f32.copysign" : wat_plaininstr

scoped syntax "f64.abs"      : wat_plaininstr
scoped syntax "f64.neg"      : wat_plaininstr
scoped syntax "f64.ceil"     : wat_plaininstr
scoped syntax "f64.floor"    : wat_plaininstr
scoped syntax "f64.trunc"    : wat_plaininstr
scoped syntax "f64.nearest"  : wat_plaininstr
scoped syntax "f64.sqrt"     : wat_plaininstr
scoped syntax "f64.add"      : wat_plaininstr
scoped syntax "f64.sub"      : wat_plaininstr
scoped syntax "f64.mul"      : wat_plaininstr
scoped syntax "f64.div"      : wat_plaininstr
scoped syntax "f64.min"      : wat_plaininstr
scoped syntax "f64.max"      : wat_plaininstr
scoped syntax "f64.copysign" : wat_plaininstr

scoped syntax "i32.eqz"  : wat_plaininstr
scoped syntax "i32.eq"   : wat_plaininstr
scoped syntax "i32.ne"   : wat_plaininstr
scoped syntax "i32.lt_s" : wat_plaininstr
scoped syntax "i32.lt_u" : wat_plaininstr
scoped syntax "i32.gt_s" : wat_plaininstr
scoped syntax "i32.gt_u" : wat_plaininstr
scoped syntax "i32.le_s" : wat_plaininstr
scoped syntax "i32.le_u" : wat_plaininstr
scoped syntax "i32.ge_s" : wat_plaininstr
scoped syntax "i32.ge_u" : wat_plaininstr

scoped syntax "i64.eqz"  : wat_plaininstr
scoped syntax "i64.eq"   : wat_plaininstr
scoped syntax "i64.ne"   : wat_plaininstr
scoped syntax "i64.lt_s" : wat_plaininstr
scoped syntax "i64.lt_u" : wat_plaininstr
scoped syntax "i64.gt_s" : wat_plaininstr
scoped syntax "i64.gt_u" : wat_plaininstr
scoped syntax "i64.le_s" : wat_plaininstr
scoped syntax "i64.le_u" : wat_plaininstr
scoped syntax "i64.ge_s" : wat_plaininstr
scoped syntax "i64.ge_u" : wat_plaininstr

scoped syntax "f32.eq" : wat_plaininstr
scoped syntax "f32.ne" : wat_plaininstr
scoped syntax "f32.lt" : wat_plaininstr
scoped syntax "f32.gt" : wat_plaininstr
scoped syntax "f32.le" : wat_plaininstr
scoped syntax "f32.ge" : wat_plaininstr

scoped syntax "f64.eq" : wat_plaininstr
scoped syntax "f64.ne" : wat_plaininstr
scoped syntax "f64.lt" : wat_plaininstr
scoped syntax "f64.gt" : wat_plaininstr
scoped syntax "f64.le" : wat_plaininstr
scoped syntax "f64.ge" : wat_plaininstr

scoped syntax "i32.wrap_i64"        : wat_plaininstr
scoped syntax "i32.trunc_f32_s"     : wat_plaininstr
scoped syntax "i32.trunc_f32_u"     : wat_plaininstr
scoped syntax "i32.trunc_f64_s"     : wat_plaininstr
scoped syntax "i32.trunc_f64_u"     : wat_plaininstr
scoped syntax "i32.trunc_sat_f32_s" : wat_plaininstr
scoped syntax "i32.trunc_sat_f32_u" : wat_plaininstr
scoped syntax "i32.trunc_sat_f64_s" : wat_plaininstr
scoped syntax "i32.trunc_sat_f64_u" : wat_plaininstr
scoped syntax "i64.extend_i32_s"    : wat_plaininstr
scoped syntax "i64.extend_i32_u"    : wat_plaininstr
scoped syntax "i64.trunc_f32_s"     : wat_plaininstr
scoped syntax "i64.trunc_f32_u"     : wat_plaininstr
scoped syntax "i64.trunc_f64_s"     : wat_plaininstr
scoped syntax "i64.trunc_f64_u"     : wat_plaininstr
scoped syntax "i64.trunc_sat_f32_s" : wat_plaininstr
scoped syntax "i64.trunc_sat_f32_u" : wat_plaininstr
scoped syntax "i64.trunc_sat_f64_s" : wat_plaininstr
scoped syntax "i64.trunc_sat_f64_u" : wat_plaininstr
scoped syntax "f32.convert_i32_s"   : wat_plaininstr
scoped syntax "f32.convert_i32_u"   : wat_plaininstr
scoped syntax "f32.convert_i64_s"   : wat_plaininstr
scoped syntax "f32.convert_i64_u"   : wat_plaininstr
scoped syntax "f32.demote_f64"      : wat_plaininstr
scoped syntax "f64.convert_i32_s"   : wat_plaininstr
scoped syntax "f64.convert_i32_u"   : wat_plaininstr
scoped syntax "f64.convert_i64_s"   : wat_plaininstr
scoped syntax "f64.convert_i64_u"   : wat_plaininstr
scoped syntax "f64.promote_f32"     : wat_plaininstr
scoped syntax "i32.reinterpret_f32" : wat_plaininstr
scoped syntax "i64.reinterpret_f64" : wat_plaininstr
scoped syntax "f32.reinterpret_i32" : wat_plaininstr
scoped syntax "f64.reinterpret_i64" : wat_plaininstr

scoped syntax "i32.extend8_s"  : wat_plaininstr
scoped syntax "i32.extend16_s" : wat_plaininstr
scoped syntax "i64.extend8_s"  : wat_plaininstr
scoped syntax "i64.extend16_s" : wat_plaininstr
scoped syntax "i64.extend32_s" : wat_plaininstr

-- todo vector instruction :)

scoped syntax "[wat_plaininstr|" wat_plaininstr "]" : term

macro_rules
| `([wat_plaininstr| unreachable]) => `(Plain.unreachable)
| `([wat_plaininstr| nop])         => `(Plain.nop)
| `([wat_plaininstr| br $l])       => `(Plain.br [wat_labelidx| $l])
| `([wat_plaininstr| br_if $l])    => `(Plain.br_if [wat_labelidx| $l])
| `([wat_plaininstr| br_table $l:wat_labelidx $ls:wat_labelidx*]) =>
    `(let l' := [wat_labelidx| $l]
      let vec := Vec.cons l' [wat_vec_labelidx| $l $ls*] sorry
      Plain.br_table (vec.dropLast) (vec.getLastD l')
    )
| `([wat_plaininstr| return])                   => `(Plain.wasm_return)
| `([wat_plaininstr| call $x:wat_funcidx])      =>
    `(Plain.call [wat_funcidx| $x])
| `([wat_plaininstr| call_indirect $x:wat_tableidx $y:wat_typeuse]) =>
    `(Plain.call_indirect [wat_tableidx| $x] [wat_typeuse| $y])
| `([wat_plaininstr| call_indirect $y:wat_typeuse]) =>
    `(Plain.call_indirect [wat_tableidx| 0] [wat_typeuse| $y])

-- Reference
macro_rules
| `([wat_plaininstr| ref.null $t:wat_heaptype]) =>
    `(Plain.reference <| .null [wat_heaptype| $t])
| `([wat_plaininstr| ref.is_null]) => `(Plain.reference <| .is_null)
| `([wat_plaininstr| ref.func $x:wat_funcidx]) =>
    `(Plain.reference <| .func [wat_funcidx| $x])

-- Parametric
macro_rules
| `([wat_plaininstr| drop]) => `(Plain.drop)
| `([wat_plaininstr| select]) => `(Plain.select .none)
| `([wat_plaininstr| select $t:wat_result*]) =>
    `(Plain.select (.some [wat_result_list| $t* ]))

-- Variadic
macro_rules
| `([wat_plaininstr| local.get $x:wat_localidx]) =>
    `(Plain.locl <| .get [wat_localidx| $x])
| `([wat_plaininstr| local.set $x:wat_localidx]) =>
    `(Plain.locl <| .set [wat_localidx| $x])
| `([wat_plaininstr| local.tee $x:wat_localidx]) =>
    `(Plain.locl <| .tee [wat_localidx| $x])
| `([wat_plaininstr| global.get $x:wat_globalidx]) =>
    `(Plain.globl <| .get [wat_globalidx| $x])
| `([wat_plaininstr| global.set $x:wat_globalidx]) =>
    `(Plain.globl <| .set [wat_globalidx| $x])

-- Tables
macro_rules
| `([wat_plaininstr| table.get $x:wat_tableidx]) =>
    `(Plain.table <| .get [wat_tableidx| $x])
| `([wat_plaininstr| table.set $x:wat_tableidx]) =>
    `(Plain.table <| .set [wat_tableidx| $x])
| `([wat_plaininstr| table.size $x:wat_tableidx]) =>
    `(Plain.table <| .size [wat_tableidx| $x])
| `([wat_plaininstr| table.grow $x:wat_tableidx]) =>
    `(Plain.table <| .grow [wat_tableidx| $x])
| `([wat_plaininstr| table.fill $x:wat_tableidx]) =>
    `(Plain.table <| .fill [wat_tableidx| $x])
| `([wat_plaininstr| table.copy $x:wat_tableidx $y:wat_tableidx]) =>
    `(Plain.table <| .copy [wat_tableidx| $x] [wat_tableidx| $y])
| `([wat_plaininstr| table.init $x:wat_tableidx $y:wat_elemidx]) =>
    `(Plain.table <| .init [wat_tableidx| $x] [wat_elemidx| $y])
| `([wat_plaininstr| elem.drop $x:wat_elemidx]) =>
    `(Plain.elem_drop [wat_elemidx| $x])
-- Table Abbreviations
| `([wat_plaininstr| table.get])  => `(Plain.table <| .get 0)
| `([wat_plaininstr| table.set])  => `(Plain.table <| .set 0)
| `([wat_plaininstr| table.size]) => `(Plain.table <| .size 0)
| `([wat_plaininstr| table.grow]) => `(Plain.table <| .grow 0)
| `([wat_plaininstr| table.fill]) => `(Plain.table <| .fill 0)
| `([wat_plaininstr| table.copy]) => `(Plain.table <| .copy 0 0)
| `([wat_plaininstr| table.init $x:wat_elemidx]) =>
    `(Plain.table <| .init 0 [wat_elemidx| $x])

-- Memory
macro_rules
| `([wat_plaininstr| i32.load $m]) =>
  `(Plain.memory <| .integer (nn:=.double) (.load [wat_memarg₄| $m]))
| `([wat_plaininstr| i64.load $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.load [wat_memarg₈| $m]))
| `([wat_plaininstr| f32.load $m]) =>
  `(Plain.memory <| .float (nn:=.double) (.load [wat_memarg₄| $m]))
| `([wat_plaininstr| f64.load $m]) =>
  `(Plain.memory <| .float (nn:=.quad) (.load [wat_memarg₈| $m]))
| `([wat_plaininstr| i32.load8_s $m]) =>
  `(Plain.memory <| .integer (nn:=.double) (.load8 .s [wat_memarg₁| $m]))
| `([wat_plaininstr| i32.load8_u $m]) =>
  `(Plain.memory <| .integer (nn:=.double) (.load8 .u [wat_memarg₁| $m]))
| `([wat_plaininstr| i32.load16_s $m]) =>
  `(Plain.memory <| .integer (nn:=.double) (.load16 .s [wat_memarg₂| $m]))
| `([wat_plaininstr| i32.load16_u $m]) =>
  `(Plain.memory <| .integer (nn:=.double) (.load16 .u [wat_memarg₂| $m]))
| `([wat_plaininstr| i64.load8_s $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.load8 .s [wat_memarg₁| $m]))
| `([wat_plaininstr| i64.load8_u $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.load8 .u [wat_memarg₁| $m]))
| `([wat_plaininstr| i64.load16_s $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.load16 .s [wat_memarg₂| $m]))
| `([wat_plaininstr| i64.load16_u $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.load16 .u [wat_memarg₂| $m]))
| `([wat_plaininstr| i64.load32_s $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.load32 .s [wat_memarg₄| $m]))
| `([wat_plaininstr| i64.load32_u $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.load32 .u [wat_memarg₄| $m]))
| `([wat_plaininstr| i32.store $m]) =>
  `(Plain.memory <| .integer (nn:=.double) (.store [wat_memarg₄| $m]))
| `([wat_plaininstr| i64.store $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.store [wat_memarg₈| $m]))
| `([wat_plaininstr| f32.store $m]) =>
  `(Plain.memory <| .float (nn:=.double) (.store [wat_memarg₄| $m]))
| `([wat_plaininstr| f64.store $m]) =>
  `(Plain.memory <| .float (nn:=.quad) (.store [wat_memarg₈| $m]))
| `([wat_plaininstr| i32.store8 $m]) =>
  `(Plain.memory <| .integer (nn:=.double) (.store8 [wat_memarg₁| $m]))
| `([wat_plaininstr| i32.store16 $m]) =>
  `(Plain.memory <| .integer (nn:=.double) (.store16 [wat_memarg₂| $m]))
| `([wat_plaininstr| i64.store8 $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.store8 [wat_memarg₁| $m]))
| `([wat_plaininstr| i64.store16 $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.store16 [wat_memarg₂| $m]))
| `([wat_plaininstr| i64.store32 $m]) =>
  `(Plain.memory <| .integer (nn:=.quad) (.store32 [wat_memarg₄| $m]))
| `([wat_plaininstr| memory.size]) => `(Plain.memory <| .size)
| `([wat_plaininstr| memory.grow]) => `(Plain.memory <| .grow)
| `([wat_plaininstr| memory.fill]) => `(Plain.memory <| .fill)
| `([wat_plaininstr| memory.copy]) => `(Plain.memory <| .copy)
| `([wat_plaininstr| memory.init $x]) =>
    `(Plain.memory <| .init [wat_dataidx| $x])
| `([wat_plaininstr| data.drop $x]) =>
    `(Plain.memory <| .data_drop [wat_dataidx| $x])

macro_rules
| `([wat_plaininstr| i32.const $n]) =>
    `(Plain.numeric (nn:=.double) <| .integer (.const [wat_i32| $n]))
| `([wat_plaininstr| i64.const $n]) =>
    `(Plain.numeric (nn:=.quad) <| .integer (.const [wat_i64| $n]))
-- todo f32/f64 const

-- some helpers to make the macro_rules shorter/more readable
@[inline] private def int nn     := Plain.numeric (nn:=nn) ∘ .integer
@[inline] private def i_unop nn  := int nn ∘ .unop
@[inline] private def i_binop nn := int nn ∘ .binop
@[inline] private def i_rel nn   := int nn ∘ .relation
@[inline] private def i_eqz nn   := int nn (.test .eqz)

@[inline] private def float nn   := Plain.numeric (nn:=nn) ∘ .float
@[inline] private def f_unop nn  := float nn ∘ .unop
@[inline] private def f_binop nn := float nn ∘ .binop
@[inline] private def f_rel nn   := float nn ∘ .relation

@[inline] private def i32_unop  := i_unop .double
@[inline] private def i32_binop := i_binop .double
@[inline] private def i32_rel   := i_rel .double
@[inline] private def i32_eqz   := i_eqz .double

@[inline] private def i64_unop  := i_unop .quad
@[inline] private def i64_binop := i_binop .quad
@[inline] private def i64_rel   := i_rel .quad
@[inline] private def i64_eqz   := i_eqz .quad

@[inline] private def f32_unop  := f_unop .double
@[inline] private def f32_binop := f_binop .double
@[inline] private def f32_rel   := f_rel .double

@[inline] private def f64_unop  := f_unop .quad
@[inline] private def f64_binop := f_binop .quad
@[inline] private def f64_rel   := f_rel .quad

@[inline] private def int32   := int .double
@[inline] private def int64   := int .quad
@[inline] private def float32 := float .double
@[inline] private def float64 := float .quad

macro_rules
| `([wat_plaininstr| i32.clz])    => `(i32_unop .clz)
| `([wat_plaininstr| i32.ctz])    => `(i32_unop .ctz)
| `([wat_plaininstr| i32.popcnt]) => `(i32_unop .popcnt)
| `([wat_plaininstr| i32.add])    => `(i32_binop .add)
| `([wat_plaininstr| i32.sub])    => `(i32_binop .sub)
| `([wat_plaininstr| i32.mul])    => `(i32_binop .mul)
| `([wat_plaininstr| i32.div_s])  => `(i32_binop (.div .s))
| `([wat_plaininstr| i32.div_u])  => `(i32_binop (.div .u))
| `([wat_plaininstr| i32.rem_s])  => `(i32_binop (.rem .s))
| `([wat_plaininstr| i32.rem_u])  => `(i32_binop (.rem .u))
| `([wat_plaininstr| i32.and])    => `(i32_binop .and)
| `([wat_plaininstr| i32.or])     => `(i32_binop .or)
| `([wat_plaininstr| i32.xor])    => `(i32_binop .xor)
| `([wat_plaininstr| i32.shl])    => `(i32_binop .shl)
| `([wat_plaininstr| i32.shr_s])  => `(i32_binop (.shr .s))
| `([wat_plaininstr| i32.shr_u])  => `(i32_binop (.shr .u))
| `([wat_plaininstr| i32.rotl])   => `(i32_binop .rotl)
| `([wat_plaininstr| i32.rotr])   => `(i32_binop .rotr)

macro_rules
| `([wat_plaininstr| i64.clz])    => `(i64_unop .clz)
| `([wat_plaininstr| i64.ctz])    => `(i64_unop .ctz)
| `([wat_plaininstr| i64.popcnt]) => `(i64_unop .popcnt)
| `([wat_plaininstr| i64.add])    => `(i64_binop .add)
| `([wat_plaininstr| i64.sub])    => `(i64_binop .sub)
| `([wat_plaininstr| i64.mul])    => `(i64_binop .mul)
| `([wat_plaininstr| i64.div_s])  => `(i64_binop (.div .s))
| `([wat_plaininstr| i64.div_u])  => `(i64_binop (.div .u))
| `([wat_plaininstr| i64.rem_s])  => `(i64_binop (.rem .s))
| `([wat_plaininstr| i64.rem_u])  => `(i64_binop (.rem .u))
| `([wat_plaininstr| i64.and])    => `(i64_binop .and)
| `([wat_plaininstr| i64.or])     => `(i64_binop .or)
| `([wat_plaininstr| i64.xor])    => `(i64_binop .xor)
| `([wat_plaininstr| i64.shl])    => `(i64_binop .shl)
| `([wat_plaininstr| i64.shr_s])  => `(i64_binop (.shr .s))
| `([wat_plaininstr| i64.shr_u])  => `(i64_binop (.shr .u))
| `([wat_plaininstr| i64.rotl])   => `(i64_binop .rotl)
| `([wat_plaininstr| i64.rotr])   => `(i64_binop .rotr)

macro_rules
| `([wat_plaininstr| f32.abs])      => `(f32_unop .abs)
| `([wat_plaininstr| f32.neg])      => `(f32_unop .neg)
| `([wat_plaininstr| f32.ceil])     => `(f32_unop .ceil)
| `([wat_plaininstr| f32.floor])    => `(f32_unop .floor)
| `([wat_plaininstr| f32.trunc])    => `(f32_unop .trunc)
| `([wat_plaininstr| f32.nearest])  => `(f32_unop .nearest)
| `([wat_plaininstr| f32.sqrt])     => `(f32_unop .sqrt)
| `([wat_plaininstr| f32.add])      => `(f32_binop .add)
| `([wat_plaininstr| f32.sub])      => `(f32_binop .sub)
| `([wat_plaininstr| f32.mul])      => `(f32_binop .mul)
| `([wat_plaininstr| f32.div])      => `(f32_binop .div)
| `([wat_plaininstr| f32.min])      => `(f32_binop .min)
| `([wat_plaininstr| f32.max])      => `(f32_binop .max)
| `([wat_plaininstr| f32.copysign]) => `(f32_binop .copysign)

macro_rules
| `([wat_plaininstr| f64.abs])      => `(f64_unop .abs)
| `([wat_plaininstr| f64.neg])      => `(f64_unop .neg)
| `([wat_plaininstr| f64.ceil])     => `(f64_unop .ceil)
| `([wat_plaininstr| f64.floor])    => `(f64_unop .floor)
| `([wat_plaininstr| f64.trunc])    => `(f64_unop .trunc)
| `([wat_plaininstr| f64.nearest])  => `(f64_unop .nearest)
| `([wat_plaininstr| f64.sqrt])     => `(f64_unop .sqrt)
| `([wat_plaininstr| f64.add])      => `(f64_binop .add)
| `([wat_plaininstr| f64.sub])      => `(f64_binop .sub)
| `([wat_plaininstr| f64.mul])      => `(f64_binop .mul)
| `([wat_plaininstr| f64.div])      => `(f64_binop .div)
| `([wat_plaininstr| f64.min])      => `(f64_binop .min)
| `([wat_plaininstr| f64.max])      => `(f64_binop .max)
| `([wat_plaininstr| f64.copysign]) => `(f64_binop .copysign)

macro_rules
| `([wat_plaininstr| i32.eqz])  => `(i32_eqz)
| `([wat_plaininstr| i32.eq])   => `(i32_rel .eq)
| `([wat_plaininstr| i32.ne])   => `(i32_rel .ne)
| `([wat_plaininstr| i32.lt_s]) => `(i32_rel (.lt .s))
| `([wat_plaininstr| i32.lt_u]) => `(i32_rel (.lt .u))
| `([wat_plaininstr| i32.gt_s]) => `(i32_rel (.gt .s))
| `([wat_plaininstr| i32.gt_u]) => `(i32_rel (.gt .u))
| `([wat_plaininstr| i32.le_s]) => `(i32_rel (.le .s))
| `([wat_plaininstr| i32.le_u]) => `(i32_rel (.le .u))
| `([wat_plaininstr| i32.ge_s]) => `(i32_rel (.ge .s))
| `([wat_plaininstr| i32.ge_u]) => `(i32_rel (.ge .u))

macro_rules
| `([wat_plaininstr| i64.eqz])  => `(i64_eqz)
| `([wat_plaininstr| i64.eq])   => `(i64_rel .eq)
| `([wat_plaininstr| i64.ne])   => `(i64_rel .ne)
| `([wat_plaininstr| i64.lt_s]) => `(i64_rel (.lt .s))
| `([wat_plaininstr| i64.lt_u]) => `(i64_rel (.lt .u))
| `([wat_plaininstr| i64.gt_s]) => `(i64_rel (.gt .s))
| `([wat_plaininstr| i64.gt_u]) => `(i64_rel (.gt .u))
| `([wat_plaininstr| i64.le_s]) => `(i64_rel (.le .s))
| `([wat_plaininstr| i64.le_u]) => `(i64_rel (.le .u))
| `([wat_plaininstr| i64.ge_s]) => `(i64_rel (.ge .s))
| `([wat_plaininstr| i64.ge_u]) => `(i64_rel (.ge .u))

macro_rules
| `([wat_plaininstr| f32.eq]) => `(f32_rel .eq)
| `([wat_plaininstr| f32.ne]) => `(f32_rel .ne)
| `([wat_plaininstr| f32.lt]) => `(f32_rel .lt)
| `([wat_plaininstr| f32.gt]) => `(f32_rel .gt)
| `([wat_plaininstr| f32.le]) => `(f32_rel .le)
| `([wat_plaininstr| f32.ge]) => `(f32_rel .ge)

macro_rules
| `([wat_plaininstr| f64.eq]) => `(f64_rel .eq)
| `([wat_plaininstr| f64.ne]) => `(f64_rel .ne)
| `([wat_plaininstr| f64.lt]) => `(f64_rel .lt)
| `([wat_plaininstr| f64.gt]) => `(f64_rel .gt)
| `([wat_plaininstr| f64.le]) => `(f64_rel .le)
| `([wat_plaininstr| f64.ge]) => `(f64_rel .ge)

macro_rules
| `([wat_plaininstr| i32.wrap_i64])        => `(int32 (.wrap_i64))
| `([wat_plaininstr| i32.trunc_f32_s])     => `(int32 (.trunc_f .double .s))
| `([wat_plaininstr| i32.trunc_f32_u])     => `(int32 (.trunc_f .double .u))
| `([wat_plaininstr| i32.trunc_f64_s])     => `(int32 (.trunc_f .quad .s))
| `([wat_plaininstr| i32.trunc_f64_u])     => `(int32 (.trunc_f .quad .u))
| `([wat_plaininstr| i32.trunc_sat_f32_s]) => `(int32 (.trunc_sat_f .double .s))
| `([wat_plaininstr| i32.trunc_sat_f32_u]) => `(int32 (.trunc_sat_f .double .u))
| `([wat_plaininstr| i32.trunc_sat_f64_s]) => `(int32 (.trunc_sat_f .quad .s))
| `([wat_plaininstr| i32.trunc_sat_f64_u]) => `(int32 (.trunc_sat_f .quad .u))

| `([wat_plaininstr| i64.extend_i32_s])    => `(int64 (.extend_i32 .s))
| `([wat_plaininstr| i64.extend_i32_u])    => `(int64 (.extend_i32 .u))
| `([wat_plaininstr| i64.trunc_f32_s])     => `(int64 (.trunc_f .double .s))
| `([wat_plaininstr| i64.trunc_f32_u])     => `(int64 (.trunc_f .double .u))
| `([wat_plaininstr| i64.trunc_f64_s])     => `(int64 (.trunc_f .quad .s))
| `([wat_plaininstr| i64.trunc_f64_u])     => `(int64 (.trunc_f .quad .u))
| `([wat_plaininstr| i64.trunc_sat_f32_s]) => `(int64 (.trunc_sat_f .double .s))
| `([wat_plaininstr| i64.trunc_sat_f32_u]) => `(int64 (.trunc_sat_f .double .u))
| `([wat_plaininstr| i64.trunc_sat_f64_s]) => `(int64 (.trunc_sat_f .quad .s))
| `([wat_plaininstr| i64.trunc_sat_f64_u]) => `(int64 (.trunc_sat_f .quad .u))

| `([wat_plaininstr| f32.convert_i32_s]) => `(float32 (.convert_i .double .s))
| `([wat_plaininstr| f32.convert_i32_u]) => `(float32 (.convert_i .double .u))
| `([wat_plaininstr| f32.convert_i64_s]) => `(float32 (.convert_i .quad .s))
| `([wat_plaininstr| f32.convert_i64_u]) => `(float32 (.convert_i .quad .u))
| `([wat_plaininstr| f32.demote_f64])    => `(float32 (.demote_f64))

| `([wat_plaininstr| f64.convert_i32_s]) => `(float64 (.convert_i .double .s))
| `([wat_plaininstr| f64.convert_i32_u]) => `(float64 (.convert_i .double .u))
| `([wat_plaininstr| f64.convert_i64_s]) => `(float64 (.convert_i .quad .s))
| `([wat_plaininstr| f64.convert_i64_u]) => `(float64 (.convert_i .quad .u))
| `([wat_plaininstr| f64.promote_f32])   => `(float64 (.promote_f32))

| `([wat_plaininstr| i32.reinterpret_f32]) => `(int32 (.reinterpret_f))
| `([wat_plaininstr| i64.reinterpret_f64]) => `(int64 (.reinterpret_f))
| `([wat_plaininstr| f32.reinterpret_i32]) => `(float32 (.reinterpret_i))
| `([wat_plaininstr| f64.reinterpret_i64]) => `(float64 (.reinterpret_i))

macro_rules
| `([wat_plaininstr| i32.extend8_s])  => `(int32 (.extend8_s))
| `([wat_plaininstr| i32.extend16_s]) => `(int32 (.extend16_s))
| `([wat_plaininstr| i64.extend8_s])  => `(int64 (.extend8_s))
| `([wat_plaininstr| i64.extend16_s]) => `(int64 (.extend16_s))
| `([wat_plaininstr| i64.extend32_s]) => `(int64 (.extend32_s))

declare_syntax_cat wat_blocktype
scoped syntax wat_result ? : wat_blocktype
scoped syntax wat_typeuse  : wat_blocktype

scoped syntax "[wat_blocktype|" wat_blocktype "]" : term

macro_rules
| `([wat_blocktype| ]) => `(Instr.BlockType.value .none)
| `([wat_blocktype| $t:wat_result]) =>
    `(Instr.BlockType.value (.some [wat_result| $t]))
| `([wat_blocktype| $x:wat_typeuse]) =>
    `(Instr.BlockType.typeuse [wat_typeuse| $x])

declare_syntax_cat wat_blockinstr
declare_syntax_cat wat_instr

scoped syntax wat_plaininstr : wat_instr
scoped syntax wat_blockinstr : wat_instr
scoped syntax "(" wat_instr ")" : wat_instr

scoped syntax "block" wat_label wat_blocktype (wat_instr)* "end" wat_ident? : wat_blockinstr
scoped syntax "loop" wat_label wat_blocktype (wat_instr)* "end" wat_ident? : wat_blockinstr
scoped syntax "if" wat_label wat_blocktype (wat_instr)* "else" wat_ident? (wat_instr)* "end" wat_ident? : wat_blockinstr
scoped syntax "if" wat_label wat_blocktype (wat_instr)* "end" wat_ident? : wat_blockinstr

scoped syntax "[wat_blockinstr|" wat_blockinstr "]" : term
scoped syntax "[wat_instr|" wat_instr "]"           : term
scoped syntax "[wat_instr_list|" wat_instr* "]"     : term

macro_rules
| `([wat_instr| $i:wat_plaininstr]) => `(Instr.plain [wat_plaininstr| $i])
| `([wat_instr| $i:wat_blockinstr]) => `(Instr.block [wat_blockinstr| $i])
| `([wat_instr| ($i:wat_instr)])    => `([wat_instr| $i])

macro_rules
| `([wat_instr_list| ]) => `([])
| `([wat_instr_list| $i:wat_instr $is:wat_instr*]) =>
    `([wat_instr| $i] :: [wat_instr_list| $is*])

macro_rules
| `([wat_blockinstr| block $l:wat_label $bt:wat_blocktype
                        $is:wat_instr* end $id]) =>
    `(Block.block [wat_label| $l] [wat_blocktype| $bt]
        [wat_instr_list| $is*] .wasm_end [wat_ident?| $id])
-- Loop
| `([wat_blockinstr| loop $l:wat_label $bt:wat_blocktype
                        $is:wat_instr* end $id]) =>
    `(Block.block [wat_label| $l] [wat_blocktype| $bt]
        [wat_instr_list| $is*] .wasm_end [wat_ident?| $id])
-- If
| `([wat_blockinstr| if $l:wat_label $bt:wat_blocktype $is₁:wat_instr*
                     else $id₁:wat_ident? $is₂:wat_instr*
                     end $id₂:wat_ident?]) =>
    `(Block.wasm_if [wat_label| $l] [wat_blocktype| $bt]
        [wat_instr_list| $is₁*]
        .wasm_else [wat_ident?| $id₁] [wat_instr_list| $is₂*]
        .wasm_end [wat_ident?| $id₂])

-- Abbreviation for If
| `([wat_blockinstr| if $l:wat_label $bt:wat_blocktype
                        $is:wat_instr* end $id]) =>
    `(Block.block [wat_label| $l] [wat_blocktype| $bt]
        [wat_instr_list| $is*]
        .wasm_else .none [] .wasm_end [wat_ident?| $id])

-- Currently broken so commented out :)
/-
declare_syntax_cat wat_foldedinstr
declare_syntax_cat wat_foldedinstr_at
scoped syntax "(" wat_foldedinstr_at ")" : wat_foldedinstr
scoped syntax "(" wat_foldedinstr_at "(" wat_foldedinstr_at ")" ")" : wat_foldedinstr

scoped syntax wat_plaininstr wat_foldedinstr : wat_foldedinstr_at
scoped syntax "block" wat_label wat_blocktype wat_instr* : wat_foldedinstr_at
scoped syntax "loop" wat_label wat_blocktype wat_instr* : wat_foldedinstr_at
scoped syntax "if" wat_label wat_blocktype wat_foldedinstr "(" "then" wat_instr* ")"
          ("(" "else" wat_instr* ")")? : wat_foldedinstr_at

scoped syntax "[wat_foldedinstr_at|" wat_foldedinstr_at "]" : term
scoped syntax "[wat_foldedinstr|" wat_foldedinstr "]" : term

macro_rules
| `([wat_foldedinstr| ($i)]) => `([wat_foldedinstr_at| $i])
-- | `([wat_foldedinstr| ($i $is) ]) =>
    -- `([wat_foldedinstr_at| $i] :: [wat_foldedinstr| $is])

macro_rules
| `([wat_foldedinstr_at| $i:wat_plaininstr $is:wat_foldedinstr]) =>
    `([wat_foldedinstr| $is] ++ [wat_plaininstr| $i])
| `([wat_foldedinstr| (block $l $bt $is:wat_instr*)]) =>
    `([wat_instr| block $l $bt $is* end])
| `([wat_foldedinstr| (loop $l $bt $is:wat_instr*)]) =>
    `([wat_instr| loop $l $bt $is* end])

macro_rules
| `([wat_foldedinstr_at| if $l $bt $cond (then $is₁*) ]) =>
    `([wat_foldedinstr| $cond] ++ [[wat_instr| if $l $bt $is₁* end]])
| `([wat_foldedinstr| (if $l $bt $cond (then $is₁*) (else $is₂*) )]) =>
    `([wat_foldedinstr| $cond]
    ++ [[wat_instr| if $l $bt $is₁* else $is₂:wat_instr* end]])

scoped syntax wat_foldedinstr : wat_instr
scoped syntax "(" wat_instr ")" : wat_instr
macro_rules
| `([wat_instr| $i:wat_foldedinstr]) => `([wat_foldedinstr| $i])
| `([wat_instr| ($i:wat_instr)]) => `([wat_instr| $i])
-/

declare_syntax_cat wat_expr
scoped syntax wat_instr* : wat_expr
scoped syntax "[wat_expr|" wat_expr "]" : term

macro_rules
| `([wat_expr| $is:wat_instr*]) => `([wat_instr_list| $is*])
