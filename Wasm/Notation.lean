/- WIP: This imports a WAT notation that can be used in Lean to build the CSTs -/

import Wasm.Text.Notation.Value
import Wasm.Text.Notation.Typ
import Wasm.Text.Notation.Index
import Wasm.Text.Notation.Instr

/- Currently only instructions/expressions can be made with the following
syntax:

```
def example := [wat_expr|
  i32.const 2
  i32.const 5
  i32.mul
]
```

Currently a little buggy atm :)
-/
