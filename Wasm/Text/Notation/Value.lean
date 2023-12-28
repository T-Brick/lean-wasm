import Numbers
import Wasm.Text.Ident

namespace Wasm.Text.Notation

open Numbers

declare_syntax_cat wat_u32
declare_syntax_cat wat_u64

declare_syntax_cat wat_s32
declare_syntax_cat wat_s33
declare_syntax_cat wat_s64

declare_syntax_cat wat_i32
declare_syntax_cat wat_i64

syntax num : wat_u32
syntax num : wat_u64

syntax num : wat_s32
syntax num : wat_s33
syntax num : wat_s64

syntax num     : wat_i32
syntax wat_u32 : wat_i32
syntax wat_s32 : wat_i32
syntax num     : wat_i64
syntax wat_u64 : wat_i64
syntax wat_s64 : wat_i64

syntax "[wat_u32|" wat_u32 "]" : term
syntax "[wat_u64|" wat_u64 "]" : term

syntax "[wat_s32|" wat_s32 "]" : term
syntax "[wat_s33|" wat_s33 "]" : term
syntax "[wat_s64|" wat_s64 "]" : term

syntax "[wat_i32|" wat_i32 "]" : term
syntax "[wat_i64|" wat_i64 "]" : term

macro_rules
| `([wat_u32| $x:num]) => `(Unsigned.ofNat (n:=⟨32, by simp⟩) $x)
| `([wat_u64| $x:num]) => `(Unsigned.ofNat (n:=⟨64, by simp⟩) $x)

| `([wat_s32| $x:num]) => `(Signed.ofNat   (n:=⟨32, by simp⟩) $x)
| `([wat_s33| $x:num]) => `(Signed.ofNat   (n:=⟨33, by simp⟩) $x)
| `([wat_s64| $x:num]) => `(Signed.ofNat   (n:=⟨64, by simp⟩) $x)

| `([wat_i32| $x:num])     => `(Unsigned.ofNat (n:=⟨32, by simp⟩) $x)
| `([wat_i32| $x:wat_u32]) => `([wat_u32| $x])
| `([wat_i32| $x:wat_s32]) => `([wat_s32| $x])
| `([wat_i64| $x:num])     => `(Unsigned.ofNat (n:=⟨64, by simp⟩) $x)
| `([wat_i64| $x:wat_u64]) => `([wat_u64| $x])
| `([wat_i64| $x:wat_s64]) => `([wat_s64| $x])


declare_syntax_cat wat_ident
declare_syntax_cat wat_ident?
syntax ident : wat_ident
syntax wat_ident ? : wat_ident?

syntax "[wat_ident_str|" ident "]" : term
syntax "[wat_ident|" wat_ident "]" : term
syntax "[wat_ident?|" wat_ident? "]" :term

/- TODO: identifiers in WAT should be preceded by a `$` but this clashes with -/
macro_rules
| `([wat_ident_str| $id:ident]) =>
  return Lean.Syntax.mkStrLit id.getId.toString
| `([wat_ident| $id:ident]) =>
  `(Ident.mk [wat_ident_str| $id] sorry sorry)
| `([wat_ident?| $id:wat_ident]) => `(.some [wat_ident| $id])
| `([wat_ident?| ]) => `(.none)


declare_syntax_cat wat_value
syntax wat_u32   : wat_value
syntax wat_u64   : wat_value
syntax wat_s32   : wat_value
syntax wat_s64   : wat_value
syntax wat_ident : wat_value
syntax str       : wat_value

syntax "[wat_value|" wat_value "]" : term

macro_rules
| `([wat_value| $n:wat_u32    ]) => `([wat_u32| $n])
| `([wat_value| $n:wat_u64    ]) => `([wat_u64| $n])
| `([wat_value| $n:wat_s32    ]) => `([wat_s32| $n])
| `([wat_value| $n:wat_s64    ]) => `([wat_s64| $n])
| `([wat_value| $id:wat_ident ]) => `([wat_ident| $id])
