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
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.0"
require Cli from git "https://github.com/mhuisi/lean4-cli" @ "1dae8b12f8ba27576ffe5ddee78bebf6458157b0"
require numbers from git
  "https://github.com/T-Brick/Numbers" @ "main"
