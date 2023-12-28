import Wasm.Text.Notation.Value
import Wasm.Text.Notation.Typ
import Wasm.Text.Index

namespace Wasm.Text.Notation

open Wasm.Text.Module

declare_syntax_cat wat_index
syntax wat_u32   : wat_index
syntax wat_ident : wat_index

syntax "[wat_index|" wat_index "]"      : term
syntax "[wat_vec_index|" wat_index* "]" : term

macro_rules
| `([wat_index| $x:wat_u32 ])    => `(Index.num [wat_u32| $x])
| `([wat_index| $id:wat_ident ]) => `(Index.name [wat_ident| $id])

macro_rules
| `([wat_vec_index| ]) => `(Vec.nil)
| `([wat_vec_index| $i:wat_index]) => `(Vec.single [wat_index| $i])
| `([wat_vec_index| $i:wat_index $is:wat_index*]) =>
    `(Vec.cons [wat_index| $i] [wat_vec_index| $is*])


/- Various indices -- these don't really matter since we check the context
    later but to try and best comply with the spec they are implemented like
    this.
 -/
declare_syntax_cat wat_typeidx
declare_syntax_cat wat_funcidx
declare_syntax_cat wat_tableidx
declare_syntax_cat wat_memidx
declare_syntax_cat wat_globalidx
declare_syntax_cat wat_elemidx
declare_syntax_cat wat_dataidx
declare_syntax_cat wat_localidx
declare_syntax_cat wat_labelidx

syntax wat_index : wat_typeidx
syntax wat_index : wat_funcidx
syntax wat_index : wat_tableidx
syntax wat_index : wat_memidx
syntax wat_index : wat_globalidx
syntax wat_index : wat_elemidx
syntax wat_index : wat_dataidx
syntax wat_index : wat_localidx
syntax wat_index : wat_labelidx

syntax "[wat_typeidx|"   wat_typeidx   "]" : term
syntax "[wat_funcidx|"   wat_funcidx   "]" : term
syntax "[wat_tableidx|"  wat_tableidx  "]" : term
syntax "[wat_memidx|"    wat_memidx    "]" : term
syntax "[wat_globalidx|" wat_globalidx "]" : term
syntax "[wat_elemidx|"   wat_elemidx   "]" : term
syntax "[wat_dataidx|"   wat_dataidx   "]" : term
syntax "[wat_localidx|"  wat_localidx  "]" : term
syntax "[wat_labelidx|"  wat_labelidx  "]" : term

syntax "[wat_vec_typeidx|"   wat_typeidx*   "]" : term
syntax "[wat_vec_funcidx|"   wat_funcidx*   "]" : term
syntax "[wat_vec_tableidx|"  wat_tableidx*  "]" : term
syntax "[wat_vec_memidx|"    wat_memidx*    "]" : term
syntax "[wat_vec_globalidx|" wat_globalidx* "]" : term
syntax "[wat_vec_elemidx|"   wat_elemidx*   "]" : term
syntax "[wat_vec_dataidx|"   wat_dataidx*   "]" : term
syntax "[wat_vec_localidx|"  wat_localidx*  "]" : term
syntax "[wat_vec_labelidx|"  wat_labelidx*  "]" : term

macro_rules
| `([wat_typeidx|   $i:wat_index ]) => `([wat_index| $i])
| `([wat_funcidx|   $i:wat_index ]) => `([wat_index| $i])
| `([wat_tableidx|  $i:wat_index ]) => `([wat_index| $i])
| `([wat_memidx|    $i:wat_index ]) => `([wat_index| $i])
| `([wat_globalidx| $i:wat_index ]) => `([wat_index| $i])
| `([wat_elemidx|   $i:wat_index ]) => `([wat_index| $i])
| `([wat_dataidx|   $i:wat_index ]) => `([wat_index| $i])
| `([wat_localidx|  $i:wat_index ]) => `([wat_index| $i])
| `([wat_labelidx|  $i:wat_index ]) => `([wat_index| $i])

macro_rules
| `([wat_vec_typeidx|   $i:wat_typeidx   $is:wat_typeidx  * ]) =>
    `(Vec.cons [wat_typeidx| $i]   [wat_vec_typeidx| $is*   ] sorry)
| `([wat_vec_funcidx|   $i:wat_funcidx   $is:wat_funcidx  * ]) =>
    `(Vec.cons [wat_funcidx| $i]   [wat_vec_funcidx| $is*   ] sorry)
| `([wat_vec_tableidx|  $i:wat_tableidx  $is:wat_tableidx * ]) =>
    `(Vec.cons [wat_tableidx| $i]  [wat_vec_tableidx| $is*  ] sorry)
| `([wat_vec_memidx|    $i:wat_memidx    $is:wat_memidx   * ]) =>
    `(Vec.cons [wat_memidx| $i]    [wat_vec_memidx| $is*    ] sorry)
| `([wat_vec_globalidx| $i:wat_globalidx $is:wat_globalidx* ]) =>
    `(Vec.cons [wat_globalidx| $i] [wat_vec_globalidx| $is* ] sorry)
| `([wat_vec_elemidx|   $i:wat_elemidx   $is:wat_elemidx  * ]) =>
    `(Vec.cons [wat_elemidx| $i]   [wat_vec_elemidx| $is*   ] sorry)
| `([wat_vec_dataidx|   $i:wat_dataidx   $is:wat_dataidx  * ]) =>
    `(Vec.cons [wat_dataidx| $i]   [wat_vec_dataidx| $is*   ] sorry)
| `([wat_vec_localidx|  $i:wat_localidx  $is:wat_localidx * ]) =>
    `(Vec.cons [wat_localidx| $i]  [wat_vec_localidx| $is*  ] sorry )
| `([wat_vec_labelidx|  $i:wat_labelidx  $is:wat_labelidx * ]) =>
    `(Vec.cons [wat_labelidx| $i]  [wat_vec_labelidx| $is*  ] sorry )

| `([wat_vec_typeidx|   ]) => `(Vec.nil)
| `([wat_vec_funcidx|   ]) => `(Vec.nil)
| `([wat_vec_tableidx|  ]) => `(Vec.nil)
| `([wat_vec_memidx|    ]) => `(Vec.nil)
| `([wat_vec_globalidx| ]) => `(Vec.nil)
| `([wat_vec_elemidx|   ]) => `(Vec.nil)
| `([wat_vec_dataidx|   ]) => `(Vec.nil)
| `([wat_vec_localidx|  ]) => `(Vec.nil)
| `([wat_vec_labelidx|  ]) => `(Vec.nil)

declare_syntax_cat wat_typeuse
syntax "(" "type" wat_typeidx ")" : wat_typeuse
syntax "(" "type" wat_typeidx ")" wat_param* wat_result* : wat_typeuse
syntax wat_param* wat_result* : wat_typeuse

syntax "[wat_typeuse|" wat_typeuse "]" : term

macro_rules
| `([wat_typeuse| (type $x)]) => `(Typeuse.type_ind [wat_typeidx| $x])
| `([wat_typeuse| (type $x) $t₁:wat_param* $t₂:wat_result*]) =>
    `(Typeuse.param_res [wat_typeidx| $x]
      [wat_param_list| $t₁*]
      [wat_result_list| $t₂*]
    )
| `([wat_typeuse| $t₁:wat_param* $t₂:wat_result*]) =>
    `(Typeuse.elab_param_res [wat_param_list| $t₁*] [wat_result_list| $t₂*])
