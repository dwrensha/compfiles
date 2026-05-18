import Lean.Data.NameMap.Basic

import Dashboard.Common
import Dashboard.Components.Base
import Dashboard.Components.Navbar
import Dashboard.Models.Contests
import Dashboard.Models.Problems
import SSG.Core
import SSG.Html
import SSG.Tags

open Html

def stringifyPercent (num : Nat) (denom : Nat) : String :=
  let p : Float := (OfNat.ofNat num) / (OfNat.ofNat denom)
  let s1 := s!"{p * 100}"
  let pos := s1.find (fun c ↦ c = '.')
  if pos = s1.endPos then
    s1 ++ "%"
  else
    let p1 : String.Pos.Raw := ⟨pos.1.1 + 3⟩
    let s2 := Substring.Raw.mk s1 0 p1
    s2.toString ++ "%"

namespace Contest

variable {idxType subIdxType : Type} [Ord idxType] [Ord subIdxType]

def problemTable (c : Contest idxType subIdxType) (config : SConfig)
  (mds : Lean.NameMap ProblemMeta)
  (fmtIdx : idxType → String) (fmtSubIdx : subIdxType → String)
  : Html := .table [cls "full-problem-grid"] <| c.mergeNeighbors.reverse.map
  fun ⟨idx, l⟩ ↦ .tr [] <| .td [cls "year"] (fmtIdx idx) :: l.map
  fun subIdx ↦
    let name := c.toName idx subIdx
    let stateCls := match mds.find? name with
    | .some detail => if detail.proved then "proved" else "formalized"
    | .none => "todo"
    .td [cls stateCls] [.a (config.resolveAbs ["problems", s!"{name}.html"]) []
      <| fmtSubIdx subIdx]

def generate (c : Contest idxType subIdxType)
  (config : SConfig) (filePath : String) (navbarState : NavbarState)
  (mds : Lean.NameMap ProblemMeta)
  (fmtIdx : idxType → String) (fmtSubIdx : subIdxType → String)
  : IO Page := pure <| Page.dynamic filePath <| pure <| renderDoc <|
  base "Compfiles: Catalog of Math Problems Formalized in Lean"
  config (currentPage := navbarState) (includeHljs := true)
  <| c.desc c.problemCount
  ++ [
    let fmtPercentage := stringifyPercent (c.formalizedCount mds) c.problemCount
    .p [] [
      .b [] s!"{c.formalizedCount mds}",
      s!" problems have been formalized ({fmtPercentage}).",
    ],
    let fmtPercentage := stringifyPercent (c.solvedCount mds) c.problemCount
    .p [] [
      .b [] s!"{c.solvedCount mds}",
      s!" problems have complete formalized solutions ({fmtPercentage}).",
    ],
    c.problemTable config mds fmtIdx fmtSubIdx,
  ]

end Contest
