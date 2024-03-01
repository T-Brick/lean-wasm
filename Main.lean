import Wasm
import Cli

def version := "24.02.2"

open Cli

inductive Wasm.Output
| wat
| wasm
deriving Inhabited

def Wasm.outputText (p : Parsed) (msg : String) : IO UInt32 := do
  match p.flag? "output" with
  | .some file =>
    let output := file.as! String
    IO.FS.writeFile output msg
    return 0
  | .none =>
    IO.println msg
    return 0

def Wasm.outputBin (p : Parsed)
                   (input : System.FilePath)
                   (data : Wasm.Binary.ByteSeq)
                   : IO UInt32 := do
  let output :=
    match p.flag? "output" with
    | .some file => file.as! String
    | .none      => input.withExtension "wasm"
  IO.FS.writeBinFile output ⟨data.toArray⟩
  return 0

def run (p : Parsed) : IO UInt32 := do

  if !p.hasPositionalArg "input" then
    panic! "Missing file argument"
  let input : System.FilePath :=
    p.positionalArg! "input" |>.as! String

  if !(← input.pathExists) then
    panic! s!"Input file does not exist: {input}"
  if ← input.isDir then
    panic! s!"Input path is a directory: {input}"

  let emit : Wasm.Output :=
    match p.flag? "emit" |>.map (·.as! String |>.toLower) with
    | .some "wasm" => .wasm
    | .some "wat"  => .wat
    | .some x      => panic! s!"Unknown emit target '{x}'!"
    | .none        => .wat

  -- must be a WASM file for now :)
  let contents ← IO.FS.readBinFile input
  let init := Wasm.Binary.Bytecode.State.new contents

  match (Wasm.Binary.Module.ofOpcode).run init with
  | (.error e, s) =>
    IO.println s!"ERROR:\n\n{e}\n---"
    IO.println s!"{String.intercalate "\n" s.log.reverse}\n"
    return 1
  | (.ok mod, s) =>
    match emit with
    | .wat => Wasm.outputText p (Wasm.Text.Module.toString mod)
    | .wasm => Wasm.outputBin p input (Wasm.Binary.Module.toOpcode mod)
  return 0

def topCmd : Cmd := `[Cli|
  wasm VIA run; [version]
  "A verified (WIP) implementation of WebAssembly"

  FLAGS:
    e, emit : String;          "Specify the output format (either WAT or WASM)"
    o, output : String;        "Specify output file"

  ARGS:
    input : String;      "The input file"
]

def main (args : List String) : IO UInt32 := topCmd.validate args
