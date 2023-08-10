import Wasm.Util
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value
import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Syntax.Module

namespace Wasm.Dynamics.Instance

structure Export where
  name  : Syntax.Value.Name
  value : Value.Extern

structure Module where
  types       : Vec Syntax.Typ.Func
  funcaddrs   : Vec Address.Function
  tableaddrs  : Vec Address.Table
  memaddrs    : Vec Address.Memory
  globaladdrs : Vec Address.Global
  elemaddrs   : Vec Address.Element
  dataaddrs   : Vec Address.Data
  exports     : Vec Instance.Export

structure Function.Internal where
  type : Syntax.Typ.Func
  module : Instance.Module
  code : Syntax.Module.Function

structure Function.Host where
  type : Syntax.Typ.Func
  hostcode : Unit         -- todo add

inductive Function
| internal : Function.Internal → Function
| host     : Function.Host → Function

structure Table where
  type : Syntax.Typ.Table
  elem : Vec Value.Reference

structure Memory where
  type : Syntax.Typ.Mem
  data : Vec Syntax.Value.Byte
  pagesize : data.length % 65536 = 0
  -- todo more invariants

-- in internal representations, the least significant byte is at the end
-- def Memory.read (mem : Memory)
                -- (pos len : Nat)
                -- : List Syntax.Value.Byte :=
  -- mem.data.list.drop pos |>.take len |>.reverse

-- def Memory.write'
    -- (mem : Memory)
    -- (bytes : Syntax.Value.Bytes)
    -- (pos : Nat)
    -- (h₁ : pos + bytes.length ≤ mem.data.length)
    -- : Memory :=
  -- match h₂ :bytes with
  -- | .fst b     => writeOne mem b ⟨pos, by
      -- simp [Syntax.Value.Bytes.length_fst, ←Nat.succ_eq_add_one] at h₁
      -- exact Nat.lt_of_succ_lt_succ (Nat.lt_succ_of_le h₁)
    -- ⟩
  -- | .cons b bs =>
    -- let last := Syntax.Value.Bytes.last bytes
    -- let bs'  := Syntax.Value.Bytes.drop_last bytes (by
        -- sorry
      -- )
    -- let pos' := ⟨pos, by
        -- rw [Syntax.Value.Bytes.length_cons] at h₁
        -- exact lt_left_add (Nat.lt_of_succ_le h₁)
      -- ⟩
    -- Memory.write' (writeOne mem last pos') bs' (pos + 1) (by
      -- simp [Syntax.Value.Bytes.length_cons, Nat.succ_eq_add_one] at h₁
      -- simp [Nat.add_assoc, Nat.add_comm 1, Vec.set, Vec.length]
      -- sorry
      -- exact h₁
    -- )
-- where writeOne (mem : Memory)
              --  (byte : Syntax.Value.Byte)
              --  (pos : Fin mem.data.length)
              --  : Memory :=
  -- let data' := mem.data.set pos byte
  -- ⟨mem.type, data', by simp [Vec.set, Vec.length]; exact mem.pagesize⟩

def Memory.write
    (mem : Memory)
    (bytes : List Syntax.Value.Byte)
    (pos : Nat)
    (h : pos + bytes.length ≤ mem.data.length)
    : Memory :=
  match bytes with
  | .nil       => mem
  | .cons b bs =>
    let pos' := ⟨pos, by
        rw [List.length_cons] at h
        exact lt_left_add (Nat.lt_of_succ_le h)
      ⟩
    let data' := mem.data.set pos' b
    let mem' : Memory := ⟨mem.type, data', by
        simp [Vec.set, Vec.length]; exact mem.pagesize
      ⟩
    Memory.write mem' bs (pos + 1) (by
      simp [List.length_cons, Nat.succ_eq_add_one] at h
      simp [Nat.add_assoc, Nat.add_comm 1, Vec.set, Vec.length]
      exact h
    )


structure Global where
  type  : Syntax.Typ.Global
  value : Value

structure Element where
  type : Syntax.Typ.Ref
  elem : Vec Value.Reference

structure Data where
  data : Vec Syntax.Value.Byte


structure Store where
  funcs   : Vec Function
  tables  : Vec Table
  mems    : Vec Memory
  globals : Vec Global
  elems   : Vec Element
  datas   : Vec Data
