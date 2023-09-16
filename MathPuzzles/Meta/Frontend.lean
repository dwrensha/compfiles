/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend

open Lean Elab Frontend

namespace Lean.Elab.IO

open System

-- TODO allow finding Lean 4 sources from the toolchain.
def findLean (mod : Name) : IO FilePath := do
  return FilePath.mk ((← findOLean mod).toString.replace "build/lib/" "") |>.withExtension "lean"

/-- Implementation of `moduleSource`, which is the cached version of this function. -/
def moduleSource' (mod : Name) : IO String := do
  IO.FS.readFile (← findLean mod)

initialize sourceCache : IO.Ref <| HashMap Name String ←
  IO.mkRef .empty

/-- Read the source code of the named module. The results are cached. -/
def moduleSource (mod : Name) : IO String := do
  let m ← sourceCache.get
  match m.find? mod with
  | some r => return r
  | none => do
    let v ← moduleSource' mod
    sourceCache.set (m.insert mod v)
    return v
