import Wasm
import Cli

def version := "0.0.1"

open Cli

def run (p : Parsed) : IO UInt32 := do

  if !p.hasPositionalArg "input" then
    panic! "Missing file argument"
  let input : System.FilePath :=
    p.positionalArg! "input" |>.as! String

  if !(← input.pathExists) then
    panic! s!"Input file does not exist: {input}"
  if ← input.isDir then
    panic! s!"Input path is a directory: {input}"

  -- must be a WASM file
  let contents ← IO.FS.readBinFile input
  let init := Wasm.Binary.Bytecode.State.new contents

  match (Wasm.Binary.Module.ofOpcode).run init with
  | (.error e, s) =>
    IO.println s!"ERROR:\n\n{e}\n---"
    IO.println s!"{String.intercalate "\n" s.log.reverse}\n"
    return 1
  | (.ok mod, s) =>
    let mod_str := Wasm.Text.Module.toString mod
    match p.flag? "output" with
    | .some file =>
      let output := file.as! String
      IO.FS.writeFile output mod_str
    | .none => IO.println mod_str

  return 0

def topCmd : Cmd := `[Cli|
  wasm VIA run; [version]
  "A verified (WIP) implementation of WebAssembly"

  FLAGS:
    -- e, emit : String;          "Specify the output format (either WAT or WASM)"
    o, output : String;        "Specify output file"

  ARGS:
    input : String;      "The input file"
]

def main (args : List String) : IO UInt32 := topCmd.validate args
