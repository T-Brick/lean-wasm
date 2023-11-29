import Wasm.Binary.Opcode
import Wasm.Syntax.Index
open Numbers

namespace Wasm.Binary.Module.Index

open Wasm.Syntax.Module.Index

instance : Opcode Typ      := ⟨toOpcode ∘ cast (by unfold Typ     ; rfl),
    Bytecode.err_log "Parsing type index." do
    let res ← ofOpcode
    return cast (by unfold Typ; rfl) res
  ⟩
instance : Opcode Function := ⟨toOpcode ∘ cast (by unfold Function; rfl),
    Bytecode.err_log "Parsing function index." do
    let res ← ofOpcode
    return cast (by unfold Function; rfl) res
  ⟩
instance : Opcode Table    := ⟨toOpcode ∘ cast (by unfold Table   ; rfl),
    Bytecode.err_log "Parsing table index." do
    let res ← ofOpcode
    return cast (by unfold Table; rfl) res
  ⟩
instance : Opcode Memory   := ⟨toOpcode ∘ cast (by unfold Memory  ; rfl),
    Bytecode.err_log "Parsing memory index." do
    let res ← ofOpcode
    return cast (by unfold Memory; rfl) res
  ⟩
instance : Opcode Global   := ⟨toOpcode ∘ cast (by unfold Global  ; rfl),
    Bytecode.err_log "Parsing global index." do
    let res ← ofOpcode
    return cast (by unfold Global; rfl) res
  ⟩
instance : Opcode Element  := ⟨toOpcode ∘ cast (by unfold Element ; rfl),
    Bytecode.err_log "Parsing element index." do
    let res ← ofOpcode
    return cast (by unfold Element; rfl) res
  ⟩
instance : Opcode Data     := ⟨toOpcode ∘ cast (by unfold Data    ; rfl),
    Bytecode.err_log "Parsing data index." do
    let res ← ofOpcode
    return cast (by unfold Data; rfl) res
  ⟩
instance : Opcode Local    := ⟨toOpcode ∘ cast (by unfold Local   ; rfl),
    Bytecode.err_log "Parsing local index." do
    let res ← ofOpcode
    return cast (by unfold Local; rfl) res
  ⟩
instance : Opcode Label    := ⟨toOpcode ∘ cast (by unfold Label   ; rfl),
    Bytecode.err_log "Parsing label index." do
    let res ← ofOpcode
    return cast (by unfold Label; rfl) res
  ⟩
