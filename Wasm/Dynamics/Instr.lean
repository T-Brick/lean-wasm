import Wasm.Syntax
import Wasm.Dynamics.Address

namespace Wasm.Dynamics

mutual
-- the List Instr can be thought of as a continuation that can be branched to
inductive Stack.Label
| label : Nat → List Instr.Dynamic → Stack.Label

inductive Instr.Dynamic
| real  : Syntax.Instr → Instr.Dynamic
| admin : Instr.Admin  → Instr.Dynamic

inductive Instr.Admin
| trap
| ref : Address.Function → Instr.Admin
| ref_extern : Dynamics.Address.Extern → Instr.Admin
| invoke : Dynamics.Address.Function → Instr.Admin
| label : Stack.Label → List Instr.Dynamic → Syntax.Instr.Pseudo → Instr.Admin
| frame : List Instr.Dynamic → List Instr.Dynamic → Syntax.Instr.Pseudo → Instr.Admin
end


