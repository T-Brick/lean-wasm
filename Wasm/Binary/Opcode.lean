import Wasm.Vec
import Wasm.Syntax.Value
import Numbers
-- import Mathlib.Data.Vector
open Numbers

namespace Wasm.Binary

abbrev Byte    := UInt8
abbrev ByteSeq := List Byte -- maybe change : )
@[inline] def Byte.toSeq : UInt8 → List UInt8 := (.cons · [])

instance : ToString ByteSeq := ⟨String.concatWith " "⟩

structure Bytecode.State where
  seq : ByteArray
  pos : Fin (seq.size + 1)
  log : List String
def Bytecode.State.new (seq : ByteArray) : Bytecode.State :=
  ⟨seq, ⟨0, by simp⟩, []⟩

structure Bytecode.Error where
  log : List String -- todo maybe change ?
instance : ToString Bytecode.Error :=
  ⟨fun err => String.intercalate "\n" err.log⟩

abbrev Bytecode := ExceptT (Bytecode.Error) (StateM Bytecode.State)

instance : Monad Bytecode := show Monad (ExceptT _ _) from inferInstance

namespace Bytecode

@[inline] def err : Bytecode α := do throw ⟨[]⟩
@[inline] def errMsg (msg : String) : Bytecode α := do throw ⟨[msg]⟩

@[inline] def err_log (msg : String) (p : Bytecode α) : Bytecode α :=
  fun state =>
    ExceptT.adapt (fun err =>
      {err with log := msg :: err.log}
    ) p state
@[inline] def err_replace (f : String → String) : Bytecode α → Bytecode α :=
    ExceptT.adapt (fun err =>
      match err.log with
      | msg :: msgs => {err with log := f msg :: msgs}
      | []          => err
    )

@[inline] def log (msg : String) : Bytecode Unit := do
  let s ← get; set {s with log := msg :: s.log}

@[inline] def pos : Bytecode Nat := do return (← get).pos

@[inline] def at_end : Bytecode Bool := do
  let s ← get
  return s.pos = s.seq.size

@[inline] def readByte : Bytecode Byte := do
  let s ← get
  let p := s.pos
  if h : p.val < s.seq.size then
    let b := s.seq.get ⟨p.val, h⟩
    let p' := ⟨p.val + 1, by simp [*]⟩
    set (Bytecode.State.mk s.seq p' s.log)
    return b
  else errMsg "Tried parsing byte but at end of sequence."

@[inline] def peekByte : Bytecode Byte := do
  let s ← get
  let p := s.pos
  if h : p.val < s.seq.size then return s.seq.get ⟨p.val, h⟩
  else errMsg "Tried peeking byte but at end of sequence."

@[inline] def takeBytes (n : Nat) : Bytecode (Vector Byte n) := do
  let s ← get
  let p := s.pos
  if h₁ : p.val < s.seq.size then
    let data := ((s.seq.toList.splitAt p).2.splitAt n).1
    if h : data.length = n then
      let p' :=
        if h : p.val + n < s.seq.size
        then ⟨p.val + n, by exact Nat.lt_succ_of_lt h⟩
        else ⟨s.seq.size, by simp⟩
      set (Bytecode.State.mk s.seq p' s.log);
      return ⟨data, h⟩
    else errMsg s!"Tried taking {n} byte(s) but reached end of sequence."
  else errMsg s!"Tried taking {n} byte(s) but at end of sequence."

partial def star (p : Bytecode α) : Bytecode (List α) := fun state => do
  match ← p state with
  | (.ok a, state')  =>
    if state'.seq.size - state'.pos.val < state.seq.size - state.pos then
      match ← star p state' with
      | (.ok as, state'') => return (.ok (a :: as), state'')
      | (.error _, _)     => return (.ok [a], state')
    else return (.error ⟨["Illegal backtracking in star."]⟩, state')
  | (.error _, _) => return (.ok [], state)
-- termination_by state.seq.size - state.pos

def opt (p : Bytecode α) : Bytecode (Option α) := fun state => do
  match ← p state with
  | (.ok a    , state') => return (.ok (.some a), state')
  | (.error _, _)       => return (.ok .none, state)

def n (v : Nat) (p : Bytecode α) : Bytecode (Vector α v) := fun state => do
  if h : v = 0 then return (.ok ⟨[], by simp [*]⟩, state) else
  have : Nat.succ (v - 1) = v := Nat.succ_pred h

  match ← p state with
  | (.ok a, state') =>
    if state'.pos.val > state.pos then
      match ← n (v - 1) p state' with
      | (.ok as, state'')     =>
        return (.ok (cast (by rw [this]) (Vector.cons a as)), state'')
      | (.error err, state'') => return (.error err, state'')
    else return (.error ⟨["Illegal backtracking in n."]⟩, state')
  | (.error err, state') => return (.error err, state')

@[inline] def backtrack (p : Bytecode α) : Bytecode α := fun state => do
  match ← p state with
  | (.ok a, s')   => return (.ok a, s')
  | (.error e, _) => return (.error e, state)

def or (p₁ p₂ : Bytecode α) : Bytecode α := fun state => do
  match ← p₁ state with
  | (.ok a   , state') => return (.ok a, state')
  | (.error _, _)      =>
    match ← p₂ state with
    | (.ok a   , state') => return (.ok a, state')
    | (.error e, state') => return (.error e, state)

instance : OrElse (Bytecode α) where
  orElse p q := or p (q ())

end Bytecode

class Opcode (α : Type) where
  toOpcode : α → ByteSeq
  ofOpcode : Bytecode α

export Opcode (toOpcode ofOpcode)
instance {α} [Opcode α] : Opcode (id α) := inferInstanceAs (Opcode α)
instance {α} [Opcode α] : Opcode (Id α) := inferInstanceAs (Opcode α)

def Byte.toOpcode : Byte → ByteSeq := ([·])
def Byte.ofOpcode : Bytecode Byte := Bytecode.readByte

nonrec def Unsigned.ofLEB128 (n : { i // 0 < i }) : Bytecode (Unsigned n) := do
  let s ← get
  let lst := s.seq.toList.drop s.pos
  let init := lst.length
  match Numbers.Unsigned.ofLEB128 n lst with
  | .none   => Bytecode.errMsg "Could not parse LEB128"
  | .some (v, rem) =>
    let dp := init - rem.length
    let pos' :=
      if h : s.pos.val + dp ≥ s.seq.size
      then ⟨s.seq.size, by simp⟩
      else ⟨s.pos + dp, by rw [not_le] at h; exact Nat.lt_add_right _ h⟩
    set (Bytecode.State.mk s.seq pos' s.log)
    return v

nonrec def Signed.ofLEB128 (n : { i // 0 < i }) : Bytecode (Signed n) := do
  let s ← get
  let lst := s.seq.toList.drop s.pos
  let init := lst.length
  match Numbers.Signed.ofLEB128 n lst with
  | .none   => Bytecode.errMsg "Could not parse LEB128"
  | .some (v, rem) =>
    let dp := init - rem.length
    let pos' :=
      if h : s.pos.val + dp ≥ s.seq.size
      then ⟨s.seq.size, by simp⟩
      else ⟨s.pos + dp, by rw [not_le] at h; exact Nat.lt_add_right _ h⟩
    set (Bytecode.State.mk s.seq pos' s.log)
    return v

-- todo: use Unsigned stuff
instance : Opcode Byte := ⟨Byte.toOpcode, Byte.ofOpcode⟩
instance : Opcode (Unsigned n) := ⟨Unsigned.toLEB128, Unsigned.ofLEB128 n⟩
instance : Opcode (Signed n)   := ⟨Signed.toLEB128  , Signed.ofLEB128 n⟩
instance : Opcode Nat          :=
  ⟨ Unsigned.toLEB128 ∘ (Unsigned.ofNat : Nat → Unsigned32)
  , do let r ← Unsigned.ofLEB128 ⟨32, by simp⟩; return r.toNat
  ⟩
instance : Opcode Wasm.Syntax.Value.Byte := ⟨Byte.toOpcode, Byte.ofOpcode⟩
instance : Opcode (Wasm.Syntax.Value.FloatN nn) := ⟨sorry, sorry⟩

nonrec def List.toOpcode [Opcode α] (list : List α) : ByteSeq :=
  toOpcode list.length ++ (list.map toOpcode).join

nonrec def Vec.toOpcode [Opcode α] (vec : Vec α) : ByteSeq :=
  toOpcode vec.length ++ (vec.list.map toOpcode).join

nonrec def Vec.ofOpcode [inst : Opcode α] : Bytecode (Vec α) :=
  Bytecode.err_log "Parsing vector." do
  let len : Unsigned32 ← ofOpcode
  Bytecode.err_log s!"Parsing vector length={len}." do
  let vector ← Bytecode.n len.toNat (inst.ofOpcode)
  return ⟨vector.toList, by
    simp [Unsigned.toNat]
    exact len.isLt
  ⟩

instance [Opcode α] : Opcode (Vec α) := ⟨Vec.toOpcode, Vec.ofOpcode⟩


def Value.Name.toOpcode (name : Wasm.Syntax.Value.Name) : ByteSeq :=
  Vec.toOpcode ⟨name.value.toUTF8.toList, sorry⟩

def Value.Name.ofOpcode : Bytecode Wasm.Syntax.Value.Name := do
  let name ← Vec.ofOpcode
  return ⟨String.fromUTF8! (name.list.toByteArray), sorry⟩

instance : Opcode Wasm.Syntax.Value.Name :=
  ⟨Value.Name.toOpcode, Value.Name.ofOpcode⟩
