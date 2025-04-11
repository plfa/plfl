/-
Copyright (c) Philip Wadler. All rights reserved.
Released under Creative Commons CC-BY License as described in file LICENSE.
Author: Philip Wadler
-/

import Std.Data.HashMap
import VersoManual
import Book

/-
BookMain: main file for plfl
-/

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open Book

partial def buildExercises (mode : Mode) (logError : String → IO Unit) (cfg : Config) (_state : TraverseState) (text : Part Manual) : IO Unit := do
  let .multi := mode
    | pure ()
  let code := (← part text  |>.run {}).snd
  let dest := cfg.destination / "example-code"
  IO.FS.createDirAll <| dest
  for ⟨fn, f⟩ in code do
    let fn := dest / fn
    fn.parent.forM IO.FS.createDirAll
    if (← fn.pathExists) then IO.FS.removeFile fn
    IO.FS.writeFile fn f

where
  part : Part Manual → StateT (HashMap String String) IO Unit
    | .mk _ _ _ intro subParts => do
      for b in intro do block b
      for p in subParts do part p
  block : Block Manual → StateT (HashMap String String) IO Unit
    | .other which contents => do
      if which.name == ``Block.savedLean then
        let .arr #[.str fn, .str code] := which.data
          | logError s!"Failed to deserialize saved Lean data {which.data}"
        modify fun saved =>
          let prior := saved[fn]?.getD ""
          saved.insert fn (prior ++ code ++ "\n")

      if which.name == ``Block.savedImport then
        let .arr #[.str fn, .str code] := which.data
          | logError s!"Failed to deserialize saved Lean import data {which.data}"
        modify fun saved =>
          let prior := saved[fn]?.getD ""
          saved.insert fn (code.trimRight ++ "\n" ++ prior)

      for b in contents do block b
    | .concat bs | .blockquote bs =>
      for b in bs do block b
    | .ol _ lis | .ul lis =>
      for li in lis do
        for b in li.contents do block b
    | .dl dis =>
      for di in dis do
        for b in di.desc do block b
    | .para .. | .code .. => pure ()


def config : Config where
  emitTeX := false
  emitHtmlSingle := false
  emitHtmlMulti := true
  htmlDepth := 2

def main := manualMain (%doc Book) (extraSteps := [buildExercises]) (config := config)
