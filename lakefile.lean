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
  "https://github.com/leanprover-community/mathlib4" @ "v4.3.0-rc1"
