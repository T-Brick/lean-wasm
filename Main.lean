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
  -- match (Wasm.Binary.Module.ofOpcode).run state with
  | (.error e, _) =>
    IO.println s!"ERROR:\n\n{e}\n---"
    return 1
  | (.ok mod, s) =>
    -- IO.println s!"Successfuly parsed bytecode!\n"
    IO.println s!"{Wasm.Text.Module.toString mod}"
    -- let mod' : Wasm.Text.Module := mod
    -- IO.println s!"POS: {s.pos}"
    -- IO.println s!"{s.seq.toList.drop s.pos}\n"
    -- IO.println s!"{String.intercalate "\n" s.log.reverse}"
    return 0

def topCmd : Cmd := `[Cli|
  wasm VIA run; [version]
  "A verified implementation of WebAssembly"

  FLAGS:
    e, emit : String;          "Specify the output format (either WAT or WASM)"
    i, input  : String;        "Specify the input format (currently only WASM)"
    o, output : String;        "Specify output file"

  ARGS:
    input : String;      "The input file"
]

def main (args : List String) : IO UInt32 := topCmd.validate args
