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

def problemId (name : Lean.Name) : String :=
  name.toString.dropPrefix "Compfiles." |>.toString

def problemPath (name : Lean.Name) (extension : String) : List String :=
  ["problems", s!"{name}{extension}"]

def problemRel (name : Lean.Name) (extension : String) : String :=
  "/".intercalate (problemPath name extension)

def problemUrl (config : SConfig) (name : Lean.Name) (extension : String) : String :=
  config.resolveAbs (problemPath name extension)

def problemHtmlRel (name : Lean.Name) : String := problemRel name ".html"

def problemHtmlUrl (config : SConfig) (name : Lean.Name) : String :=
  problemUrl config name ".html"

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
    [.p [] ["The problem was imported from ", .a url [cls "external"] text, "."]]
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
    [.p [] ["The solution was imported from ", .a url [cls "external"] text, "."]]
  else []

def videos (m : ProblemExtraction.ProblemFileMetadata) : List Html :=
  if m.videos.length > 0 then
    [.div [] ["Video: ", .ul [cls "video-links"] <|
      m.videos.map fun v ↦ .li [] [.a v [] v]]]
  else []

variable {idxType subIdxType : Type} [Ord idxType] [Ord subIdxType]
  {C : Contest idxType subIdxType}

def probLeanRelName (name : Lean.Name) : String := problemRel name ".lean"

def solLeanRelName (name : Lean.Name) : String := problemRel name ".sol.lean"

def probLeanRel (p : ProblemInfo C) : String := probLeanRelName p.leanName

def solLeanRel (p : ProblemInfo C) : String := solLeanRelName p.leanName

def liveLeanForName (config : SConfig) (name : Lean.Name) (proved : Bool) : List Html
  := List.singleton <| .div [] [
  "Open with the in-brower editor at live.lean-lang.org:",
  let soldesc := if proved then "complete solution" else "in-progress solution"
  let liveLeanUrl := fun u ↦ s!"https://live.lean-lang.org/#url={uriEncodeComponent u}"
  .ul [cls "live-links"] [
    .li [] [.a (liveLeanUrl <| problemUrl config name ".lean")
      [] "problem statement only"],
    .li [] [.a (liveLeanUrl <| problemUrl config name ".sol.lean")
      [] soldesc],
  ]
]

def liveLean (config : SConfig) (p : ProblemInfo C) (proved : Bool) : List Html :=
  liveLeanForName config p.leanName proved

def writeupList (links : List WriteupLink) : List Html :=
  let writeups := links.map fun w ↦
    .li [] [.a w.url [cls "external"] w.text]
  if writeups.length > 0 then
    [.div [] ["External resources:", .ul [cls "writeups"] writeups]]
  else
    []

def writeups (p : ProblemInfo C) : List Html :=
  writeupList (C.externalUrls p.idx p.subIdx)

def Problem.generateStub (p : ProblemInfo C) : List Html := [
  .h2 [] [.text <| problemId p.leanName],
  .p [] [.text "This problem has not been formalized yet!"],
  .p [] [.text "To add a formalization of it, submit a pull request to the ",
    .a "https://github.com/dwrensha/compfiles" [cls "external"]
      [.text "Compfiles Github repository"]],
] ++ writeups p

def Problem.generateFormalized (config : SConfig) (name : Lean.Name)
  (detail : ProblemMeta) (writeupLinks : List WriteupLink) : IO (List Page) := do
  let probId := problemId name
  let metadata := detail.metadata
  let mut pages := []
  -- HTML page
  let htmlPage := Page.dynamic (problemHtmlRel name) <| pure <| renderDoc <| base
    probId config
    (currentPage := .none) (includeHljs := true) <| [
      .h2 [] probId,
      .pre [cls "problem"] [.code [cls "language-lean"] detail.problemSrc],
    ]
    ++ (if ¬ metadata.authors.isEmpty then [
      .p [cls "authors"] [s!"File author(s): {", ".intercalate metadata.authors}"],
    ] else [])
    ++ [
      .p [] ["This problem ", .a (solutionUrl probId) [cls "external"] <|
        if detail.proved then
          "has a complete formalized solution"
        else
          "does not yet have a complete formalized solution", "."]]
    ++ problemImports metadata
    ++ solutionImports metadata
    ++ videos metadata
    ++ liveLeanForName config name detail.proved
    ++ writeupList writeupLinks
  pages := htmlPage :: pages
  -- .lean file
  pages := (Page.static (probLeanRelName name) <|
    metadata.copyrightHeader ++ detail.problemSrc) :: pages
  -- .sol.lean file
  pages := (Page.static (solLeanRelName name) <|
    metadata.copyrightHeader ++ detail.solutionSrc) :: pages
  return pages

def Problem.generate (config : SConfig) (p : ProblemInfo C) : IO (List Page) := do
  let name := p.leanName
  let probId := problemId name
  match p.detail with
  | .none => return [Page.dynamic (problemHtmlRel name) <| pure <| renderDoc <| base probId config
    (currentPage := .none) (includeHljs := true) <| Problem.generateStub p]
  | .some detail =>
    Problem.generateFormalized config name detail (C.externalUrls p.idx p.subIdx)

namespace Contest

def generateProblems {idxType subIdxType : Type} [Ord idxType] [Ord subIdxType]
  (c : Contest idxType subIdxType) (config : SConfig)
  (mds : Lean.NameMap ProblemMeta)
  : IO <| List Page := do
  IO.println s!"Collecting contest: {c.fullName}"
  let mut pages : List Page := []
  for ⟨idx, subIdx⟩ in c.problems do
    let name := c.toName idx subIdx
    let info : ProblemInfo c := {
      idx := idx
      subIdx := subIdx
      detail := mds.get? name
    }
    pages := pages ++ (← Problem.generate config info)
  return pages

end Contest
