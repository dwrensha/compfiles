import Dashboard.Components.Base
import Dashboard.Models.Problems
import Dashboard.Pages.ProblemPage
import ProblemExtraction
import SSG.Html
import SSG.Tags

open Html

def problemTagClass (tag : ProblemExtraction.ProblemTag) : String :=
  (ToString.toString tag).toLower.replace " " "-"

def problemTable (config : SConfig)
  (mdsArray : Array <| Lean.Name × ProblemMeta)
  : Html := .table [cls "problems"] [
  .thead [] [.tr [] [
    .th [] "problem",
    .th [] "solved",
    .th [] "tags",
  ]],
  .tbody [] (mdsArray.map fun ⟨rawName, metadata⟩ ↦
    let name := rawName.toString.dropPrefix "Compfiles." |>.toString
    .tr [] [
    -- title=informal (sic) ???
    .td [("title", metadata.informal), cls "problem-page-link"] [
      -- TODO: DRY with toId
      .a (config.resolveAbs ["problems", s!"{name}.html"]) [] name,
    ],
    .td [cls "solved-col"] [
      .a s!"https://github.com/dwrensha/compfiles/blob/main/Compfiles/{name}.lean"
        [] [
          if metadata.proved then
            .span [("title", "complete solution")] "✅"
          else
            .span [("title", "incomplete or missing solution")] "❌"
        ]
    ],
    .td [cls "tags-col"] <| metadata.metadata.tags.map fun tg ↦ .span
      [cls s!"problem-tag {problemTagClass tg}"] s!"{tg}"
  ]).toList,
]

def All.generate (config : SConfig)
  (numProved : Nat) (mdsArray : Array <| Lean.Name × ProblemMeta)
  : IO Page := pure <| Page.dynamic "all.html" <| pure <| renderDoc <|
    base "Compfiles: Catalog of Math Problems Formalized in Lean"
    config (currentPage := .all) (includeHljs := true) [
  .p [] [.b [] s!"{mdsArray.size}", " problems have been formalized."],
  .p [] [.b [] s!"{numProved}", " problems have complete formalized solutions."],
  problemTable config mdsArray,
]
