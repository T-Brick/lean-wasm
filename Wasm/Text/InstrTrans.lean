/- Encoding of defintion WASM's instruction defintion:
    https://webassembly.github.io/spec/core/text/instructions.html
-/


-- TODO WORK IN PROGRESS

import Wasm.Syntax.Instr
import Wasm.Text.Typ
import Wasm.Text.Ident
import Wasm.Text.Index
import Wasm.Text.Instr

namespace Wasm.Text

open Wasm.Text.Module Wasm.Text.Instr

def Label.add : Label → Trans Unit
  | .name v   => do
    let s ← get
    match s.I.labels.indexOf? (.some v) with
    | .none   => Trans.updateI { s.I with labels := .some v :: s.I.labels }
    | .some i =>
      Trans.updateI { s.I with labels := .some v :: s.I.labels.set i .none }
  | .no_label => do
    let s ← get
    Trans.updateI { s.I with labels := .none :: s.I.labels }

namespace Instr

def Reference.trans : Instr.Reference → Trans Syntax.Instr.Reference
  | .null t  => return .null t
  | .is_null => return .is_null
  | .func x  => return .func (← ofText x)
instance : OfText Instr.Reference Syntax.Instr.Reference := ⟨Reference.trans⟩

def Local.trans : Instr.Local → Trans Syntax.Instr.Local
  | .get i => return .get (← ofText i)
  | .set i => return .set (← ofText i)
  | .tee i => return .tee (← ofText i)
instance : OfText Instr.Local Syntax.Instr.Local := ⟨Local.trans⟩

def Global.trans : Instr.Global → Trans Syntax.Instr.Global
  | .get i => return .get (← ofText i)
  | .set i => return .get (← ofText i)
instance : OfText Instr.Global Syntax.Instr.Global := ⟨Global.trans⟩

def Table.trans : Instr.Table → Trans Syntax.Instr.Table
  | .get x    => return .get  (← ofText x)
  | .set x    => return .set  (← ofText x)
  | .size x   => return .size (← ofText x)
  | .grow x   => return .grow (← ofText x)
  | .fill x   => return .fill (← ofText x)
  | .copy x y => return .copy (← ofText x) (← ofText y)
  | .init x y => return .init (← ofText x) (← ofText y)
instance : OfText Instr.Table Syntax.Instr.Table := ⟨Table.trans⟩

def Memory.trans : Instr.Memory → Trans Syntax.Instr.Memory
  | .integer i   => return .integer i
  | .float f     => return .float f
  | .size        => return .size
  | .grow        => return .grow
  | .fill        => return .fill
  | .copy        => return .copy
  | .init d      => return .init (← ofText d)
  | .data_drop d => return .data_drop (← ofText d)
instance : OfText Instr.Memory Syntax.Instr.Memory := ⟨Memory.trans⟩

end Instr

def Instr.Plain.trans : Instr.Plain → Trans Syntax.Instr
| .numeric n         => return .numeric n
| .reference r       => return .reference (← ofText r)
-- Parametric
| .drop              => return .drop
| .select s          => return .select s
| .locl l            => return .locl (← ofText l)
| .globl g           => return .globl (← ofText g)
| .table t           => return .table (← ofText t)
| .elem_drop e       => return .elem_drop (← ofText e)
| .memory m          => return .memory (← ofText m)
-- Control
| .nop               => return .nop
| .unreachable       => return .unreachable
| .br l              => return .br (← ofText l)
| .br_if l           => return .br_if (← ofText l)
| .br_table ls l     => return .br_table (← ofText ls) (← ofText l)
| .wasm_return       => return .wasm_return
| .call f            => return .call (← ofText f)
| .call_indirect x y => return .call_indirect (← ofText x) (← ofText y)
instance : OfText Instr.Plain Syntax.Instr := ⟨Instr.Plain.trans⟩

def Instr.BlockType.trans : Instr.BlockType → Trans Wasm.Syntax.Instr.BlockType
| .value t => return .value t
| .typeuse tu => do
  let I := (← get).I
  let x : Wasm.Syntax.Module.Index.Typ ← ofText tu
  let s' ← get
  if s'.I.locals.all (Option.isNone) then
    Trans.updateI I
    return .index x
  Trans.Error.errMsg "Parameters in block type cannot be named!"
instance : OfText Instr.BlockType Wasm.Syntax.Instr.BlockType :=
  ⟨Instr.BlockType.trans⟩

mutual
def Instr.Block.trans : Instr.Block → Trans Wasm.Syntax.Instr
  | .block lbl bt ins wend id => do
    let s ← get
    let bt'  ← ofText bt
    Label.add lbl
    let ins' ← Instr.List.trans ins
    match wend with
    | .wasm_end => do
      let _ ← (do   -- check id and label match
        if let some _ := id then
          if id ≠ lbl.toOption then
            Trans.Error.errMsg s!"Block end label {id} doesn't match start {lbl.toOption}."
          else (pure () : Trans Unit)
        pure ())
      Trans.updateI s.I -- restore context
      return .block bt' ins' wend
    | _ => Trans.Error.errMsg s!"Block cannot be terminated by {wend}."

  | .loop lbl bt ins wend id => do
    let s ← get
    let bt'  ← ofText bt
    Label.add lbl
    let ins' ← Instr.List.trans ins
    match wend with
    | .wasm_end =>
      let _ ← (do   -- check id and label match
        if let some _ := id then
          if id ≠ lbl.toOption then
            Trans.Error.errMsg s!"Loop end label {id} doesn't match start {lbl.toOption}."
          else (pure () : Trans Unit)
        pure ())
      Trans.updateI s.I -- restore context
      return .loop bt' ins' wend

    | _ => Trans.Error.errMsg s!"Loop cannot be terminated by {wend}."

  | .wasm_if lbl bt ins₁ welse id₁ ins₂ wend id₂ => do
    let s ← get
    let bt'  ← ofText bt
    Label.add lbl
    let ins₁' ← Instr.List.trans ins₁
    match welse with
    | .wasm_else =>
      let _ ← (do   -- check id and label match
        if let some _ := id₁ then
          if id₁ ≠ lbl.toOption then
            Trans.Error.errMsg s!"Else label {id₁} doesn't match start {lbl.toOption}."
          else (pure () : Trans Unit)
        pure ())
      let ins₂' ← Instr.List.trans ins₂
      match wend with
      | .wasm_end =>
        let _ ← (do   -- check id and label match
          if let some _ := id₂ then
            if id₂ ≠ lbl.toOption then
              Trans.Error.errMsg s!"If end label {id₂} doesn't match start {lbl.toOption}."
            else (pure () : Trans Unit)
          pure ())
        Trans.updateI s.I -- restore context
        return .wasm_if bt' ins₁' welse ins₂' wend
      | _ => Trans.Error.errMsg s!"If cannot be terminated by {wend}."
    | _ => Trans.Error.errMsg s!"If-then body cannot be terminated by {wend}."

def Instr.trans : Instr → Trans Wasm.Syntax.Instr
  | .plain i   => ofText i
  | .block b   => Instr.Block.trans b
  | .comment _ => return .nop -- todo : maybe change this?

def Instr.List.trans : List Instr → Trans (List Wasm.Syntax.Instr)
  | .nil       => return []
  | .cons x xs => return (← Instr.trans x) :: (← Instr.List.trans xs)
end

instance : OfText Instr.Block Wasm.Syntax.Instr         := ⟨Instr.Block.trans⟩
instance : OfText Instr Wasm.Syntax.Instr               := ⟨Instr.trans⟩
instance : OfText (List Instr) (List Wasm.Syntax.Instr) := ⟨Instr.List.trans⟩
instance : OfText Expr Wasm.Syntax.Expr :=
  ⟨fun e => do return (← Instr.List.trans e, .wasm_end)⟩

end Wasm.Text
