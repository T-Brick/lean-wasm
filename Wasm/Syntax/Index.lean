/- WASM Module indices
  https://webassembly.github.io/spec/core/syntax/modules.html#indices
-/

import Wasm.Syntax.Value
import Numbers
open Numbers

namespace Wasm.Syntax.Module.Index

abbrev Typ       := Unsigned32
abbrev Function  := Unsigned32
abbrev Table     := Unsigned32
abbrev Memory    := Unsigned32
abbrev Global    := Unsigned32
abbrev Element   := Unsigned32
abbrev Data      := Unsigned32
abbrev Local     := Unsigned32
abbrev Label     := Unsigned32
