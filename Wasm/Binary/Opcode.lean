namespace Wasm

class ToOpcode (α : Type u) where
  toOpcode : α → UInt8

instance {α} [ToOpcode α] : ToOpcode (id α) :=
  inferInstanceAs (ToOpcode α)

instance {α} [ToOpcode α] : ToOpcode (Id α) :=
  inferInstanceAs (ToOpcode α)
