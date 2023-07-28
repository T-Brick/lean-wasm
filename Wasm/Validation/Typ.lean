/- https://webassembly.github.io/spec/core/valid/types.html -/

import Wasm.Syntax.Typ
import Wasm.Syntax.Index
import Wasm.Syntax.Value
import Wasm.Syntax.Instr
import Wasm.Validation.Context

namespace Wasm.Validation.Typ

open Syntax

inductive Limit : Syntax.Typ.Limit → UInt32 → Prop
| minOnly : n ≤ k → Limit ⟨n, .none⟩ k
| minMax  : n ≤ k → m ≤ k → n ≤ m → Limit ⟨n, .some m⟩ k

inductive Block.Index (Γ : Context) : Module.Index.Typ → Syntax.Typ.Func → Prop
| typeIndex : Γ.types.list.get i = f → Block.Index Γ (Vec.index Γ.types i) f

inductive Block.ValType (Γ : Context) : Option Typ.Val → Syntax.Typ.Func → Prop
| valTypeEmpty : Block.ValType Γ .none ⟨[], []⟩
| valTypeValue : Block.ValType Γ (.some v) ⟨[], [v]⟩

inductive Block (Γ : Context) : Syntax.Typ.BlockType → Syntax.Typ.Func → Prop
| index : Block.Index Γ index type → Block Γ (.index index) type
| value : Block.ValType Γ valtype type → Block Γ (.value valtype) type

inductive Function : Syntax.Typ.Func → Prop
| func : Function ⟨τ1, τ2⟩

inductive Table : Syntax.Typ.Table → Prop
| table : Limit limit ((Vec.max_length) - 1 |>.toUInt32) → Table ⟨limit, ref⟩

inductive Memory : Syntax.Typ.Mem → Prop
| memory : Limit limit ((Nat.pow 2 16) |>.toUInt32) → Memory limit

inductive Global : Syntax.Typ.Global → Prop
| globl : Global ⟨m, valtype⟩

inductive External : Syntax.Typ.Extern → Prop
| func  : Function f → External (.func f)
| table : Table t    → External (.table t)
| mem   : Memory m   → External (.mem m)
| globl : Global g   → External (.globl g)


inductive Import.Limit : Syntax.Typ.Limit → Syntax.Typ.Limit → Prop
| empty : n1 ≥ n2 → Import.Limit ⟨n1, m1⟩ ⟨n2, .none⟩
| nonempty : n1 ≥ n2 → m1 ≤ m2 → Import.Limit ⟨n1, .some m1⟩ ⟨n2, .some m2⟩

inductive Import.Function : Syntax.Typ.Func → Syntax.Typ.Func → Prop
| refl : Import.Function f f

inductive Import.Table : Syntax.Typ.Table → Syntax.Typ.Table → Prop
| table : Import.Limit limit1 limit2 → Import.Table ⟨limit1, reftype⟩ ⟨limit2, reftype⟩

inductive Import.Memory : Syntax.Typ.Mem → Syntax.Typ.Mem → Prop
| mem : Import.Limit limit1 limit2 → Import.Memory limit1 limit2

inductive Import.Global : Syntax.Typ.Global → Syntax.Typ.Global → Prop
| refl : Import.Global g g
