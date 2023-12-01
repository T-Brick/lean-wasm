import Wasm.Vec
import Wasm.Dynamics.Address
import Wasm.Dynamics.Value
import Wasm.Dynamics.Instance
import Wasm.Dynamics.Stack
import Wasm.Syntax.Typ
import Wasm.Syntax.Value
import Wasm.Syntax.Module
import Wasm.Syntax.Index

namespace Wasm.Dynamics.Context

inductive Block : Nat → Type
| hole : List Dynamics.Value → List Instr.Dynamic → Block 0
| step : List Dynamics.Value → Stack.Label → Block k → {i : Syntax.Instr.Pseudo // i = .wasm_end} → List Instr.Dynamic → Block (k + 1)

def Thread := Stack.Frame × List Instr.Dynamic
def Config := Instance.Store × Thread

inductive Evaluation
| nil
| val   : List Dynamics.Value → Evaluation → List Instr.Dynamic → Evaluation
| label : Stack.Label → Evaluation → {i : Syntax.Instr.Pseudo // i = .wasm_end} → Evaluation
