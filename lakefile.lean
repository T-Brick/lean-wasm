import Lake
open Lake DSL

package wasm {
  -- add package configuration options here
}

lean_lib Wasm {
  -- add library configuration options here
}

-- @[defaultTarget]
lean_exe wasm {
  root := `Main
}

-- require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "a01c6e8349fe03af04862c81d64c9d6f975351c8"
