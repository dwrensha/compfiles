import Dashboard.Components.Base
import Dashboard.Models.Problems
import ProblemExtraction
import SSG.Core
import SSG.Html
import SSG.Util

/-! Problem page template -/

def solutionUrl (id : String) : String :=
  s!"https://github.com/dwrensha/compfiles/blob/main/Compfiles/{id}.lean"

open Html

def problemImports (m : ProblemExtraction.ProblemFileMetadata) : List Html :=
  if let .some url := m.problemImportedFrom then
    let text :=
      if url.startsWith "https://github.com/"
      then let rest := (url.dropPrefix "https://github.com/").toString
            match rest.splitOn "/" with
            | _ns :: repo :: _blob :: _branch :: rest =>
              "/".intercalate (repo :: rest)
            | _ => url
      else url
    [.p [] "The problem was imported from ", .a url [cls "external"] text, "."]
  else []

def solutionImports (m : ProblemExtraction.ProblemFileMetadata) : List Html :=
  if let .some url := m.solutionImportedFrom then
    let text :=
      if url.startsWith "https://github.com/"
      then let rest := (url.dropPrefix "https://github.com/").toString
            match rest.splitOn "/" with
            | _ns :: repo :: _blob :: _branch :: rest =>
              "/".intercalate (repo :: rest)
            | _ => url
      else url
    [.p [] "The solution was imported from ", .a url [cls "external"] text, "."]
  else []

def videos (m : ProblemExtraction.ProblemFileMetadata) : List Html :=
  if m.videos.length > 0 then
    [.div [] ["Video", .ul [cls "video-links"] <| m.videos.map fun v ↦ .a v [] v]]
  else []

variable {idxType subIdxType : Type} [Ord idxType] [Ord subIdxType]
  {C : Contest idxType subIdxType}

def probLeanRel (p : ProblemInfo C) : String := s!"problems/{p.leanName}.lean"

def solLeanRel (p : ProblemInfo C) : String := s!"problems/{p.leanName}.sol.lean"

def liveLean (config : SConfig) (p : ProblemInfo C) (proved : Bool) : List Html
  := List.singleton <| .div [] [
  "Open with the in-brower editor at live.lean-lang.org:",
  let soldesc := if proved then "complete solution" else "in-progress solution"
  let liveLeanUrl := fun u ↦ s!"https://live.lean-lang.org/#url={uriEncodeComponent u}"
  .ul [cls "live-links"] [
    .li [] [.a (liveLeanUrl <| config.resolveAbs [probLeanRel p])
      [] "problem statement only"],
    .li [] [.a (liveLeanUrl <| config.resolveAbs [solLeanRel p])
      [] soldesc],
  ]
]

def writeups (p : ProblemInfo C) : List Html :=
  let writeups := C.externalUrls p.idx p.subIdx |>.map fun w ↦
    .li [] [.a w.url [cls "external"] w.text]
  if writeups.length > 0 then
    [.div [] ["External resources:", .ul [cls "writeups"] writeups]]
  else
    []

def Problem.generateStub (p : ProblemInfo C) : List Html := [
  .h2 [] [.text <| p.leanName.toString.dropPrefix "Compfiles." |>.toString],
  .p [] [.text "This problem has not been formalized yet!"],
  .p [] [.text "To add a formalization of it, submit a pull request to the",
    .a "https://github.com/dwrensha/compfiles" [cls "external"]
      [.text "Compfiles Github repository"]],
] ++ (let writeupLinks := C.externalUrls p.idx p.subIdx
  if writeupLinks.length > 0 then [
    .div [] [.text "External resources:", .ul [cls "writeups"] <|
      writeupLinks.map (fun wl ↦ .li [] [.a wl.url [cls "external"] [.text wl.text]])]
  ] else [])

def Problem.generate (config : SConfig) (p : ProblemInfo C) : IO (List Page) := do
  let htmlPath := s!"problems/{p.leanName}.html"
  -- sic
  let probId := C.toName p.idx p.subIdx |>.toString.dropPrefix "Compfiles." |>.toString
  match p.detail with
  | .none => return [Page.dynamic htmlPath <| pure <| renderDoc <| base probId config
    (currentPage := .none) (includeHljs := true) <| Problem.generateStub p]
  | .some detail =>
  let metadata := detail.metadata
  let mut pages := []
  -- HTML page
  let htmlPage := Page.dynamic htmlPath <| pure <| renderDoc <| base
    (p.leanName.toString.dropPrefix "Compfiles." |>.toString) config
    (currentPage := .none) (includeHljs := true) <| [
      .h2 [] probId,
      .pre [cls "problem"] [.code [cls "language-lean"] detail.problemSrc],
    ] ++ if ¬ metadata.authors.isEmpty then [
      .p [cls "authors"] [s!"File author(s): {", ".intercalate metadata.authors}"],
    ] else [] ++ [
      .p [] ["This problem ", .a (solutionUrl probId) [cls "external"] <|
        if detail.proved then
          "has a complete formalized solution"
        else
          "does not yet have a complete formalized solution", "."]]
    ++ problemImports metadata
    ++ solutionImports metadata
    ++ videos metadata
    ++ liveLean config p detail.proved
    ++ writeups p
  pages := htmlPage :: pages
  -- .lean file
  pages := (Page.static (probLeanRel p) <|
    metadata.copyrightHeader ++ detail.problemSrc) :: pages
  -- .sol.lean file
  pages := (Page.static (solLeanRel p) <|
    metadata.copyrightHeader ++ detail.solutionSrc) :: pages
  return pages

namespace Contest

def generateProblems {idxType subIdxType : Type} [Ord idxType] [Ord subIdxType]
  (c : Contest idxType subIdxType) (config : SConfig)
  (mdsRef : IO.Ref <| Lean.NameMap ProblemMeta)
  : IO <| List Page := do
  IO.println s!"Collecting contest: {c.fullName}"
  let mut pages : List Page := []
  for ⟨idx, subIdx⟩ in c.problems do
    let name := c.toName idx subIdx
    let info : ProblemInfo c := {
      idx := idx
      subIdx := subIdx
      detail := ← mdsRef.modifyGet fun m => (m.find? name, m.erase name)
    }
    pages := pages ++ (← Problem.generate config info)
  return pages

end Contest
