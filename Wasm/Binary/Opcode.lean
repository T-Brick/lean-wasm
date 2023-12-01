import Wasm.Util
import Wasm.Syntax.Value
import Numbers
import Mathlib.Data.Vector
open Numbers

namespace Wasm.Binary

abbrev Byte    := UInt8
abbrev ByteSeq := List Byte -- maybe change : )
@[inline] def Byte.toSeq : UInt8 → List UInt8 := (.cons · [])

instance : ToString ByteSeq := ⟨String.concatWith " "⟩

structure Bytecode.State where
  seq : ByteSeq
  pos : Nat
def Bytecode.State.new : ByteSeq → Bytecode.State := (Bytecode.State.mk · 0)

structure Bytecode.Error where
  log : List String -- todo maybe change ?
instance : ToString Bytecode.Error :=
  ⟨fun err => String.intercalate "\n" err.log.reverse⟩

abbrev Bytecode := ExceptT (Bytecode.Error) (StateM Bytecode.State)

instance : Monad Bytecode := show Monad (ExceptT _ _) from inferInstance

namespace Bytecode

@[inline] def err : Bytecode α := do throw ⟨[]⟩
@[inline] def errMsg (msg : String) : Bytecode α := do throw ⟨[msg]⟩

@[inline] def err_log (msg : String) : Bytecode α → Bytecode α :=
    ExceptT.adapt (fun err =>
      {err with log := msg :: err.log}
    )
@[inline] def err_replace (f : String → String) : Bytecode α → Bytecode α :=
    ExceptT.adapt (fun err =>
      match err.log with
      | msg :: msgs => {err with log := f msg :: msgs}
      | []          => err
    )

@[inline] def pos : Bytecode Nat := do return (← get).pos

@[inline] def readByte : Bytecode Byte := do
  let s ← get
  match s.seq with
  | b :: bs => set (Bytecode.State.mk bs (s.pos + 1)); return b
  | []      => errMsg "Tried parsing byte but stream empty."

@[inline] def peekByte : Bytecode Byte := do
  match (← get).seq with
  | b :: _ => return b
  | []     => errMsg "Tried peeking byte but stream empty."

-- returns the old byte
@[inline] def modifyByte (f : Byte → Byte) : Bytecode Byte := do
  let s ← get
  match s.seq with
  | b :: bs => set (Bytecode.State.mk (f b :: bs) s.pos); return b
  | []      => errMsg "Tried modifying byte but stream empty."

def star (p : Bytecode α) : Bytecode (List α) := fun state => do
  match ← p state with
  | (.ok a, state')  =>
    if state'.pos < state.pos then
      match ← star p state' with
      | (.ok as, state'') => return (.ok (a :: as), state'')
      | (.error _, _)     => return (.ok [a], state')
    else return (.error ⟨["Illegal backtracking in star."]⟩, state')
  | (.error _, _) => return (.ok [], state)
termination_by star p s => s.pos

def opt (p : Bytecode α) : Bytecode (Option α) := fun state => do
  match ← p state with
  | (.ok a    , state') => return (.ok (.some a), state')
  | (.error _, _)       => return (.ok .none, state)

def n (v : Nat) (p : Bytecode α) : Bytecode (Vector α v) := fun state => do
  if h : v = 0 then return (.ok ⟨[], by simp [*]⟩, state) else
  have : Nat.succ (v - 1) = v := Nat.succ_pred h

  match ← p state with
  | (.ok a, state') =>
    if state'.pos < state.pos then
      match ← n (v - 1) p state' with
      | (.ok as, state'')     =>
        return (.ok (cast (by simp [this]) (Vector.cons a as)), state'')
      | (.error err, state'') => return (.error err, state'')
    else return (.error ⟨["Illegal backtracking in n."]⟩, state')
  | (.error err, state') => return (.error err, state')

def or (p₁ p₂ : Bytecode α) : Bytecode α := fun state => do
  match ← p₁ state with
  | (.ok a    , state') => return (.ok a, state')
  | (.error _, _)       =>
    match ← p₂ state with
    | (.ok a   , state') => return (.ok a, state')
    | (.error e, state') => return (.error e, state')

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

-- todo: use Unsigned stuff
instance : Opcode Byte := ⟨Byte.toOpcode, Byte.ofOpcode⟩
instance : Opcode (Unsigned n) := ⟨sorry, sorry⟩
instance : Opcode (Signed n)   := ⟨sorry, sorry⟩
instance : Opcode Nat          := ⟨sorry, sorry⟩
instance : Opcode Wasm.Syntax.Value.Byte := ⟨Byte.toOpcode, Byte.ofOpcode⟩
instance : Opcode (Wasm.Syntax.Value.FloatN nn) := ⟨sorry, sorry⟩

nonrec def List.toOpcode [Opcode α] (list : List α) : ByteSeq :=
  toOpcode list.length ++ (list.map toOpcode).join

nonrec def Vec.toOpcode [Opcode α] (vec : Vec α) : ByteSeq :=
  toOpcode vec.length ++ (vec.list.map toOpcode).join

nonrec def Vec.ofOpcode [Opcode α] : Bytecode (Vec α) := do
  let len : Unsigned32 ← ofOpcode
  let mut vec := Vec.nil
  for i in [:len.toNat] do
    let val : α ← ofOpcode
    vec := Vec.cons val vec (by sorry)

  return vec.reverse

instance [Opcode α] : Opcode (Vec α) := ⟨Vec.toOpcode, Vec.ofOpcode⟩


def Value.Name.toOpcode (name :Wasm.Syntax.Value.Name) : ByteSeq :=
  name.value.toUTF8.toList

def Value.Name.ofOpcode : Bytecode Wasm.Syntax.Value.Name := do
  let name ← Vec.ofOpcode
  return ⟨String.fromUTF8Unchecked (name.list.toByteArray), sorry⟩

instance : Opcode Wasm.Syntax.Value.Name :=
  ⟨Value.Name.toOpcode, Value.Name.ofOpcode⟩
