import Lake
open Lake DSL

package wasm {
  -- add package configuration options here
}

lean_lib Wasm {
  -- add library configuration options here
}

@[default_target]
lean_exe wasm {
  root := `Main
}

-- require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.5.0-rc1"
require Cli from git "https://github.com/mhuisi/lean4-cli" @ "nightly"
require numbers from git
  "https://github.com/T-Brick/Numbers" @ "main"
