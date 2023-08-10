/- https://webassembly.github.io/spec/core/valid/modules.html -/

import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Data.List.Join
import Wasm.Syntax.Typ
import Wasm.Syntax.Index
import Wasm.Syntax.Value
import Wasm.Syntax.Instr
import Wasm.Syntax.Module
import Wasm.Validation.Context
import Wasm.Validation.Typ
import Wasm.Validation.Statics

namespace Wasm.Validation.Module

open Syntax
open Syntax.Module
open Statics

inductive Function : (Γ : Context) → Function → Typ.Func → Prop
| function : {h : t1.length + t.list.length < Vec.max_length}
           → Γ.types.list.get x = ⟨t1, t2⟩
           → Expr {Γ with locals := Vec.append ⟨t1, by apply lt_left_add h⟩ t h
                        , labels := ⟨[t2], by simp⟩
                        , wasm_return := .some t2
                        } expr t2
           → Function Γ ⟨Vec.index Γ.types x, t, expr⟩ ⟨t1, t2⟩

inductive Table : (Γ : Context) → Table → Syntax.Typ.Table → Prop
| table : Validation.Typ.Table type → Table Γ ⟨type⟩ type

inductive Memory : (Γ : Context) → Memory → Syntax.Typ.Mem → Prop
| table : Validation.Typ.Memory type → Memory Γ ⟨type⟩ type

inductive Global : (Γ : Context) → Global → Syntax.Typ.Global → Prop
| globl : Validation.Typ.Global ⟨m, t⟩
        → Expr Γ expr [t]
        → Expr.Constant Γ expr
        → Global Γ ⟨⟨m, t⟩, expr⟩ ⟨m, t⟩

inductive Element.Mode : (Γ : Context) → Element.Mode → Syntax.Typ.Ref → Prop
| passive     : Mode Γ .passive t
| active      : Γ.tables.list.get x = ⟨limits, t⟩
              → Expr Γ expr [.num .i32]
              → Expr.Constant Γ expr
              → Mode Γ (.active (Vec.index Γ.tables x) expr) t
| declarative : Mode Γ .declarative t

inductive Element : (Γ : Context) → Element → Syntax.Typ.Ref → Prop
| nil  : Element.Mode Γ mode t
       → Element Γ ⟨t, Vec.nil, mode⟩ t
| cons : {h : List.length exprs.list + 1 < Vec.max_length}
       → Expr Γ expr [.ref t]
       → Expr.Constant Γ expr
       → Element Γ ⟨t, exprs, mode⟩ t
       → Element Γ ⟨t, Vec.cons expr exprs h, mode⟩ t

inductive Data.Mode : (Γ : Context) → Data.Mode → Prop
| passive : Mode Γ .passive
| active  : Γ.mems.list.get x = limits
          → Expr Γ expr [.num .i32]
          → Expr.Constant Γ expr
          → Mode Γ (.active (Vec.index Γ.mems x) expr)

inductive Data : (Γ : Context) → Data → Prop
| data : Data.Mode Γ mode → Data Γ ⟨b, mode⟩

inductive Start : (Γ : Context) → Start → Prop
| start : Γ.funcs.list.get x = ⟨[],[]⟩ → Start Γ ⟨Vec.index Γ.funcs x⟩

inductive Export.Description : (Γ : Context) → Export.Description → Typ.Extern → Prop
| func  : Γ.funcs.list.get x = type
        → Description Γ (.func (Vec.index Γ.funcs x)) (.func type)
| table : Γ.tables.list.get x = type
        → Description Γ (.table (Vec.index Γ.tables x)) (.table type)
| mem   : Γ.mems.list.get x = type
        → Description Γ (.mem (Vec.index Γ.mems x)) (.mem type)
| globl : Γ.globals.list.get x = type
        → Description Γ (.globl (Vec.index Γ.globals x)) (.globl type)

inductive Export : (Γ : Context) → Export → Typ.Extern → Prop
| exprt : Export.Description Γ desc type → Export Γ ⟨name, desc⟩ type

inductive Import.Description : (Γ : Context) → Import.Description → Typ.Extern → Prop
| func  : Γ.funcs.list.get x = ⟨t1, t2⟩
        → Description Γ (.func (Vec.index Γ.funcs x)) (.func ⟨t1, t2⟩)
| table : Validation.Typ.Table type
        → Description Γ (.table type) (.table type)
| mem   : Validation.Typ.Memory type
        → Description Γ (.mem type) (.mem type)
| globl : Validation.Typ.Global type
        → Description Γ (.globl type) (.globl type)

inductive Import : (Γ : Context) → Import → Typ.Extern → Prop
| imprt : Import.Description Γ desc type → Import Γ ⟨name1, name2, desc⟩ type

def Function.Index.Instr (instr : Syntax.Instr) : Option Index.Function :=
  match instr with
  | .call funcidx
  | .reference (.func funcidx) => .some funcidx
  | _ => .none

def Function.Index.Instrs (expr : List Syntax.Instr)
                          (h₁ : expr.length < Vec.max_length)
                          : (res : Vec Index.Function)
                            ×' (res.list.length ≤ expr.length) :=
  match expr with
  | .nil       => ⟨Vec.nil, by simp⟩
  | .cons i is =>
    let ⟨v, len⟩ := Function.Index.Instrs is (by rw [List.length_cons] at h₁; apply lt_left_add h₁)
    match Function.Index.Instr i with
    | .none => ⟨v, by rw [List.length_cons]; apply Nat.le_succ_of_le len⟩
    | .some index =>
      let ⟨res, vlen⟩ := Vec.length_cons index v (by
        rw [List.length_cons] at h₁
        apply le_trans_lt (Nat.succ_le_succ len) h₁
      )
      ⟨res, by rw [List.length_cons, vlen]; apply Nat.succ_le_succ len⟩

def Function.Index.List (globals : List Syntax.Instr)
                        (elems   : List Syntax.Instr)
                        (exports : List Index.Function)
                        (len : globals.length + elems.length + exports.length < Vec.max_length)
                        : Vec Index.Function :=
  let ⟨gidx, glen⟩ := Index.Instrs globals (by rw [Nat.add_assoc] at len; apply lt_left_add len)
  let ⟨eidx, elen⟩ := Index.Instrs elems (by rw [Nat.add_right_comm] at len; apply lt_add_left len)
  let xidx : Vec Index.Function := ⟨exports, by apply lt_add_left len⟩
  let gelen := by exact le_trans_lt (Nat.add_le_add glen elen) (lt_left_add len)
  let ⟨geidx, gelen⟩ := Vec.length_append gidx eidx gelen
  Vec.append geidx xidx (by
    have xlen : xidx.list.length = exports.length := by rfl
    have h := Nat.add_le_add (Nat.add_le_add glen elen) (Nat.le_of_eq xlen)
    rw [gelen]
    exact le_trans_lt h len
  )

def Function.Index (globals : Vec Syntax.Module.Global)
                   (elems   : Vec Syntax.Module.Element)
                   (exports : Vec Syntax.Module.Export)
                   : Vec Index.Function :=
  let globals_lst := globals.list.map (fun g => g.init.fst) |>.join
  let elems_lst   := elems.list.map (fun e => e.init.list.map (fun (exp, _) => exp)) |>.join |>.join
  let has_index   := (fun x =>
      match x.desc with
      | .func idx => .some idx
      | _ => .none
    )
  let exports_lst := exports.list.filterMap has_index
  let exports_len : exports_lst.length < Vec.max_length := by
    exact le_trans_lt (List.length_filterMap_le has_index exports.list) exports.maxLen
  let res := Function.Index.List globals_lst elems_lst exports_lst sorry
  res

inductive Concat : (Γ : Context) → (Judgement : Context → α → β → Prop) → List α → List β → Prop
| nil  : Concat Γ Judgement [] []
| cons : Judgement Γ a b
       → Concat Γ Judgement as bs
       → Concat Γ Judgement (a :: as) (b :: bs)

inductive ConcatOk : (Γ : Context) → (Judgement : Context → α → Prop) → List α → Prop
| nil  : ConcatOk Γ Judgement []
| cons : Judgement Γ a
       → ConcatOk Γ Judgement as
       → ConcatOk Γ Judgement (a :: as)

inductive OptionOk : (Γ : Context) → (Judgement : Context → α → Prop) → Option α → Prop
| none : OptionOk Γ Judgement .none
| some : Judgement Γ a → OptionOk Γ Judgement (.some a)

inductive DisjointNames : List Value.Name → Prop
| nil  : DisjointNames []
| cons : name ∉ names → DisjointNames names → DisjointNames (name :: names)

inductive Module : Module → List Typ.Extern → List Typ.Extern → Prop
| module : {funcsMax   : List.length (Typ.Extern.funcs it) + List.length ft < Vec.max_length}
         → {tablesMax  : List.length (Typ.Extern.tables it) + List.length tt < Vec.max_length}
         → {memsMax    : List.length (Typ.Extern.mems it) + List.length mt' < Vec.max_length}
         → {globalsMax : List.length (Typ.Extern.globals it) + List.length gt < Vec.max_length}
         → {elemsMax   : List.length rt < Vec.max_length}
         → (C : Context) =
              { types       := type
              , funcs       := Vec.append
                                ⟨Typ.Extern.funcs it, lt_left_add funcsMax⟩
                                ⟨ft, lt_add_left funcsMax⟩
                                funcsMax
              , tables      := Vec.append
                                ⟨Typ.Extern.tables it, lt_left_add tablesMax⟩
                                ⟨tt, lt_add_left tablesMax⟩
                                tablesMax
              , mems        := Vec.append
                                ⟨Typ.Extern.mems it, lt_left_add memsMax⟩
                                ⟨mt', lt_add_left memsMax⟩
                                memsMax
              , globals     := Vec.append
                                ⟨Typ.Extern.globals it, lt_left_add globalsMax⟩
                                ⟨gt, lt_add_left globalsMax⟩
                                globalsMax
              , elems       := ⟨rt, elemsMax⟩
              , datas       := data.map (fun _ => ())
              , locals      := Vec.nil
              , labels      := Vec.nil
              , wasm_return := .none
              , refs        := Function.Index globl elem exprt
              }
         → (C' : Context) =
              { types       := Vec.nil
              , funcs       := C.funcs
              , tables      := Vec.nil
              , mems        := Vec.nil
              , globals     := ⟨Typ.Extern.globals it, lt_left_add globalsMax⟩
              , elems       := Vec.nil
              , datas       := Vec.nil
              , locals      := Vec.nil
              , labels      := Vec.nil
              , wasm_return := .none
              , refs        := C.refs
              }
         → mem.list.length ≤ 1
         → DisjointNames (exprt.list.map (fun e => e.name))
         → ConcatOk C (fun (_ : Context) => Validation.Typ.Function) type.list
         → Concat C  Validation.Module.Function func.list ft
         → Concat C' Validation.Module.Table table.list tt
         → Concat C' Validation.Module.Memory mem.list mt'
         → Concat C' Validation.Module.Global globl.list gt
         → Concat C' Validation.Module.Element elem.list rt
         → ConcatOk C' Validation.Module.Data data.list
         → OptionOk C Validation.Module.Start strt
         → Concat C' Validation.Module.Import imprt.list it
         → Concat C' Validation.Module.Export exprt.list et
         → Module ⟨type, func, table, mem, globl, elem, data, strt, imprt, exprt⟩ it et
