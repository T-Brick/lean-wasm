import Wasm.Util
import Wasm.Syntax.Value
import Numbers
open Numbers

namespace Wasm.Binary

abbrev Byte    := UInt8
abbrev ByteSeq := List Byte -- maybe change : )

def Byte.toSeq : UInt8 → List UInt8 := (.cons · [])

instance : Coe Byte ByteSeq := ⟨Byte.toSeq⟩

class Opcode (α : Type u) where
  toOpcode : α → ByteSeq
  ofOpcode : ByteSeq → Option (α × ByteSeq)

export Opcode (toOpcode ofOpcode)

instance {α} [Opcode α] : Opcode (id α) := inferInstanceAs (Opcode α)
instance {α} [Opcode α] : Opcode (Id α) := inferInstanceAs (Opcode α)

-- todo: use Unsigned stuff
instance : Opcode (Unsigned n) := ⟨sorry, sorry⟩
instance : Opcode (Signed n)   := ⟨sorry, sorry⟩
instance : Opcode Nat          := ⟨sorry, sorry⟩
instance : Opcode (Wasm.Syntax.Value.FloatN nn) := ⟨sorry, sorry⟩

nonrec def List.toOpcode [Opcode α] (list : List α) : ByteSeq :=
  toOpcode list.length ++ (list.map toOpcode).join

nonrec def Vec.toOpcode [Opcode α] (vec : Vec α) : ByteSeq :=
  toOpcode vec.length ++ (vec.list.map toOpcode).join

nonrec def Vec.ofOpcode [Opcode α] (bytes : ByteSeq)
    : Option (Vec α × ByteSeq) := do
  let lenbytes : Unsigned32 × ByteSeq ← ofOpcode bytes

  let mut vec := Vec.nil
  let mut bytes := lenbytes.2
  for i in [:lenbytes.1.toNat] do
    let valbytes : α × ByteSeq ← ofOpcode bytes
    bytes := valbytes.2

    vec := Vec.cons valbytes.1 vec (by
        sorry
      )

  return (vec.reverse, bytes)

instance [Opcode α] : Opcode (Vec α) := ⟨Vec.toOpcode, Vec.ofOpcode⟩
