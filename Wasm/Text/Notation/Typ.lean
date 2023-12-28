/- This is just a test for trying out meta-programmings
 -/
import Wasm.Text.Notation.Value
import Wasm.Syntax.Typ
import Wasm.Text.Typ

namespace Wasm.Text.Notation

open Numbers Wasm.Text Wasm.Syntax.Typ

/- Num Types -/
declare_syntax_cat wat_numtype
scoped syntax "i32" : wat_numtype
scoped syntax "i64" : wat_numtype
scoped syntax "f32" : wat_numtype
scoped syntax "f64" : wat_numtype

scoped syntax "[wat_numtype|" wat_numtype "]" : term

macro_rules
| `([wat_numtype| i32 ]) => `(Wasm.Syntax.Typ.Num.i32   )
| `([wat_numtype| i64 ]) => `(Wasm.Syntax.Typ.Num.i64   )
| `([wat_numtype| f32 ]) => `(Wasm.Syntax.Typ.Num.f32   )
| `([wat_numtype| f64 ]) => `(Wasm.Syntax.Typ.Num.f64   )


/- Vector Types -/
declare_syntax_cat wat_vectype
scoped syntax "v128" : wat_vectype

scoped syntax "[wat_vectype|" wat_vectype "]" : term

macro_rules
| `([wat_vectype| v128 ]) => `(Wasm.Syntax.Typ.Vec.v128)


/- Reference Types -/
declare_syntax_cat wat_reftype
declare_syntax_cat wat_heaptype
scoped syntax "funcref"   : wat_reftype
scoped syntax "externref" : wat_reftype

scoped syntax "func"   : wat_heaptype
scoped syntax "extern" : wat_heaptype

scoped syntax "[wat_reftype|" wat_reftype "]"   : term
scoped syntax "[wat_heaptype|" wat_heaptype "]" : term

macro_rules
| `([wat_reftype| funcref   ]) => `(Wasm.Syntax.Typ.Ref.func  )
| `([wat_reftype| externref ]) => `(Wasm.Syntax.Typ.Ref.extern)

macro_rules
| `([wat_heaptype| func   ]) => `(Wasm.Syntax.Typ.Ref.func  )
| `([wat_heaptype| extern ]) => `(Wasm.Syntax.Typ.Ref.extern)


/- Value Types -/
declare_syntax_cat wat_valtype
scoped syntax wat_numtype : wat_valtype
scoped syntax wat_vectype : wat_valtype
scoped syntax wat_reftype : wat_valtype

scoped syntax "[wat_valtype|" wat_valtype "]" : term

macro_rules
| `([wat_valtype| $t:wat_numtype]) => `(Val.num [wat_numtype| $t])
| `([wat_valtype| $t:wat_vectype]) => `(Val.vec [wat_vectype| $t])
| `([wat_valtype| $t:wat_reftype]) => `(Val.ref [wat_reftype| $t])


/- Parameters -/
declare_syntax_cat wat_param_core
declare_syntax_cat wat_param
scoped syntax "(" "param" wat_valtype ")"          : wat_param_core
scoped syntax "(" "param" (wat_ident)? wat_valtype ")" : wat_param_core

scoped syntax "(" "param" wat_valtype* ")" : wat_param
scoped syntax wat_param_core               : wat_param

scoped syntax "[wat_param_core|" wat_param_core "]" : term
scoped syntax "[wat_param|" wat_param "]"           : term
scoped syntax "[wat_param_list|" wat_param* "]"     : term

macro_rules
| `([wat_param_core| (param $t:wat_valtype)]) =>
    `(Typ.Param.mk .none [wat_valtype| $t])
| `([wat_param_core| (param $id:wat_ident $t:wat_valtype)]) =>
    `(Typ.Param.mk (.some [wat_ident| $id]) [wat_valtype| $t])

macro_rules
| `([wat_param| (param $t:wat_valtype $ts:wat_valtype)]) =>
    `([wat_param_core| (param $t)] :: [wat_param| (param $ts)])
| `([wat_param| (param $t:wat_valtype )]) =>
    `([[wat_param_core| (param $t)]])
| `([wat_param| (param )]) => `([]) -- todo: double check this is valid
| `([wat_param| $p:wat_param_core]) =>
    `([wat_param_core| $p])

macro_rules
| `([wat_param_list| ]) => `([])
| `([wat_param_list| $p:wat_param]) => `([[wat_param| $p]])
| `([wat_param_list| $p:wat_param $ps:wat_param*]) =>
    `([wat_param| $p] :: [wat_param_list| $ps*])


/- Results -/
declare_syntax_cat wat_result_core
declare_syntax_cat wat_result
scoped syntax "(" "result" wat_valtype ")"  : wat_result_core

scoped syntax wat_result_core               : wat_result
scoped syntax "(" "result" wat_valtype* ")" : wat_result

scoped syntax "[wat_result_core|" wat_result_core "]" : term
scoped syntax "[wat_result|" wat_result "]"           : term
scoped syntax "[wat_result_list|" wat_result* "]"     : term

macro_rules
| `([wat_result_core| (result $t:wat_valtype)]) => `([wat_valtype| $t])

macro_rules
| `([wat_result| (result $r:wat_valtype $rs:wat_valtype)]) =>
    `([wat_result_core| (result $r)] :: [wat_result| (result $rs)])
| `([wat_result| (result $t:wat_valtype )]) =>
    `([[wat_result_core| (result $t)]])
| `([wat_result| (result )]) => `([]) -- todo: double check this is valid
| `([wat_result| $r:wat_result_core]) =>
    `([wat_result_core| $r])

macro_rules
| `([wat_result_list| ]) => `([])
| `([wat_result_list| $r:wat_result]) => `([[wat_result| $r]])
| `([wat_result_list| $r:wat_result $rs:wat_result*]) =>
    `([wat_result| $r] :: [wat_result_list| $rs*])


/- Functions -/
declare_syntax_cat wat_functype
scoped syntax "(" "func" wat_param* wat_result* ")" : wat_functype
scoped syntax "[wat_functype|" wat_functype "]" : term
macro_rules
| `([wat_functype| (func $t₁:wat_param* $t₂:wat_result*)]) =>
    `(Typ.Func.mk [wat_param_list| $t₁*] [wat_result_list| $t₂*])


/- Limits -/
declare_syntax_cat wat_limits
scoped syntax wat_u32     : wat_limits
scoped syntax wat_u32 wat_u32 : wat_limits

scoped syntax "[wat_limits|" wat_limits "]" : term

macro_rules
| `([wat_limits| $n:wat_u32 ]) =>
    `(Wasm.Syntax.Typ.Limit.mk [wat_u32| $n] .none)
| `([wat_limits| $n:wat_u32 $m:wat_u32 ])  =>
    `(Wasm.Syntax.Typ.Limit.mk [wat_u32| $n] (.some [wat_u32| $m]))


/- Memory Types -/
declare_syntax_cat wat_memtype
scoped syntax wat_limits : wat_memtype

scoped syntax "[wat_memtype|" wat_memtype "]" : term

macro_rules
| `([wat_memtype| $lim:wat_limits]) => `([wat_limits| $lim])


/- Table Types -/
declare_syntax_cat wat_tabletype
scoped syntax wat_limits wat_reftype : wat_tabletype

scoped syntax "[wat_tabletype|" wat_tabletype "]" : term

macro_rules
| `([wat_tabletype| $lim:wat_limits $et:wat_reftype]) =>
    `(Typ.Table.mk [wat_limits| $lim] [wat_reftype| $et])


declare_syntax_cat wat_globaltype
scoped syntax wat_valtype               : wat_globaltype
scoped syntax "(" "mut" wat_valtype ")" : wat_globaltype

scoped syntax "[wat_globaltype|" wat_globaltype "]" : term

macro_rules
| `([wat_globaltype| $t:wat_valtype]) => `(Global.mk Mut.const [wat_valtype| $t])
| `([wat_globaltype| (mut $t:wat_valtype)]) =>
    `(Global.mk Mut.var [wat_valtype| $t])
