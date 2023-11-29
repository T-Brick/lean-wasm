import Wasm.Binary.Opcode
import Wasm.Syntax.Index
open Numbers

namespace Wasm.Binary.Module.Index

open Wasm.Syntax.Module.Index

instance : Opcode Typ      := ⟨toOpcode ∘ cast (by unfold Typ     ; rfl),
  fun x => do
    let resb ← ofOpcode x
    return (cast (by unfold Typ     ; rfl) resb.1, resb.2)
  ⟩
instance : Opcode Function := ⟨toOpcode ∘ cast (by unfold Function; rfl),
  fun x => do
    let resb ← ofOpcode x
    return (cast (by unfold Function; rfl) resb.1, resb.2)
  ⟩
instance : Opcode Table    := ⟨toOpcode ∘ cast (by unfold Table   ; rfl),
  fun x => do
    let resb ← ofOpcode x
    return (cast (by unfold Table   ; rfl) resb.1, resb.2)
  ⟩
instance : Opcode Memory   := ⟨toOpcode ∘ cast (by unfold Memory  ; rfl),
  fun x => do
    let resb ← ofOpcode x
    return (cast (by unfold Memory; rfl) resb.1, resb.2)
  ⟩
instance : Opcode Global   := ⟨toOpcode ∘ cast (by unfold Global  ; rfl),
  fun x => do
    let resb ← ofOpcode x
    return (cast (by unfold Global  ; rfl) resb.1, resb.2)
  ⟩
instance : Opcode Element  := ⟨toOpcode ∘ cast (by unfold Element ; rfl),
  fun x => do
    let resb ← ofOpcode x
    return (cast (by unfold Element ; rfl) resb.1, resb.2)
  ⟩
instance : Opcode Data     := ⟨toOpcode ∘ cast (by unfold Data    ; rfl),
  fun x => do
    let resb ← ofOpcode x
    return (cast (by unfold Data    ; rfl) resb.1, resb.2)
  ⟩
instance : Opcode Local    := ⟨toOpcode ∘ cast (by unfold Local   ; rfl),
  fun x => do
    let resb ← ofOpcode x
    return (cast (by unfold Local   ; rfl) resb.1, resb.2)
  ⟩
instance : Opcode Label    := ⟨toOpcode ∘ cast (by unfold Label   ; rfl),
  fun x => do
    let resb ← ofOpcode x
    return (cast (by unfold Label   ; rfl) resb.1, resb.2)
  ⟩
