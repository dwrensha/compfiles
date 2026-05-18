import Dashboard.Components.Base
import Dashboard.Components.CompAnchor
import Dashboard.Contests.Imo
import Dashboard.Contests.Usamo
import Dashboard.Models.Contests
import Dashboard.Models.Problems
import Dashboard.Pages.ProblemPage
import SSG.Html
import SSG.Tags

import ProblemExtraction

open Html ProblemExtraction.ProblemTag

namespace Contest

def compRow {idxType subIdxType : Type} [Ord idxType] [Ord subIdxType]
  (config : SConfig)
  (contest : Contest idxType subIdxType) (filePath : List String)
  (mds : Lean.NameMap ProblemMeta) : Html := .tr [] [
  .th [] <| compAnchor config contest.fullName filePath,
    .td [] s!"{contest.problemCount}",
    .td [] s!"{contest.formalizedCount mds}",
    .td [] s!"{contest.solvedCount mds}",
]

end Contest

def compTable (rows : List <| Html)
  : Html := .table [cls "toplevel-olympiad-stats"] [
  .thead [] [.tr [] [
    .th [] [],
    .th [("title", "This total includes problems not added to Compfiles.")] "Total",
    .th [] "Formalized",
    .th [] "Solved"
  ]],
  .tbody [] rows,
]

def tagTable (tagFormalizedCounts : Array Nat) (tagSolvedCounts : Array Nat)
  : Html := .table [cls "toplevel-tag-stats"] [
  .thead [] [.tr [] [
    .th [] [],
    .th [] "Formalized",
    .th [] "Solved",
  ]],
  .tbody [] <| [
    .Algebra, .NumberTheory, .Combinatorics, .Geometry, .Inequality,
  ].map fun (t : ProblemExtraction.ProblemTag) ↦ .tr [] [
    .th [] s!"{t}",
    .td [] s!"{tagFormalizedCounts[t.toNat]!}",
    .td [] s!"{tagSolvedCounts[t.toNat]!}"
  ]
]

def faq (config : SConfig) : List Html := [
  .h3 [] ["Frequently Asked Questions"],
  .h4 [] ["Why are you doing this?"],
  .ul [] [
    .li [] ["It's a fun way to learn about math and mechanized reasoning!"],
    .li [] [
      "It uncovers missing pieces of theory that ought to be in ",
      .a "https://github.com/leanprover-community/mathlib4"
        [cls "external"] ["Mathlib"],
      ". See for example Joseph Myers's ",
      .a "https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry/near/321396912"
        [cls "external"] ["Euclidean geometry TODO list"],
      "."
    ],
    .li [] [
      "It's a (small) first step toward solving the ",
      .a "https://imo-grand-challenge.github.io/"
        [cls "external"] ["IMO Grand Challenge"],
      "."
    ]
  ],
  .h4 [] [
    "Why is Compfiles a separate project when ",
    .a "https://github.com/leanprover-community/mathlib4/tree/master/Archive/Imo"
      [cls "external"] ["Mathlib/Archive/Imo"],
    " already exists?"
  ],
  .p [] [
    "We want to minimize the burden that we place on Mathlib's maintainers and infrastructure. ",
    "Mathlib is a large enough monolith already. ",
    "Since Mathlib and Compfiles are both open source under the Apache-2.0 license, ",
    "it should be straightforward to move code back and forth between them, if desired."
  ],
  .h4 [] [
    "How does Compfiles compare to ",
    .a "https://github.com/openai/miniF2F" [cls "external"] ["MiniF2F"],
    "?"
  ],
  .p [] [
    "MiniF2F is a static benchmark for machine learning, with 488 math problems ",
    "formalized in multiple languages (Lean, Metamath, Isabelle, and HOL Light) ",
    "including a relatively small number of formalized solutions. ",
    "Compfiles is a continually-growing archive of math problems formalized in Lean, ",
    "with emphasis placed on complete formalized solutions."
  ],
  .h4 [] ["How does Compfiles encode problems that ask for data values to be determined?"],
  .p [] [
    "We have special ",
    .code [] ["determine"],
    " command to mark such data. You can see it in action for Imo2015P5 ",
    .a "https://github.com/dwrensha/compfiles/blob/16ce9a86e9e1c147482b264a6bbdbd4cd605a93e/Compfiles/Imo2015P5.lean#L25"
      [] ["in the source code"],
    " and ",
    .a (config.resolveRel ["problems/Compfiles.Imo2015P5.html"])
      [] ["on the rendered webpage"],
    ", and you can see its definition ",
    .a "https://github.com/dwrensha/compfiles/blob/16ce9a86e9e1c147482b264a6bbdbd4cd605a93e/ProblemExtraction.lean#L245-L252"
      [] ["here"],
    "."
  ],
  .h4 [] ["I noticed an error on this website. How do I report it?"],
  .p [] [
    "Please open an issue ",
    .a "https://github.com/dwrensha/compfiles/issues" [cls "external"] ["on Github"],
    "."
  ]
]

def Index.generate (config : SConfig)
  (tagFormalizedCounts : Array Nat) (tagSolvedCounts : Array Nat)
  (numProved : Nat) (mds : Lean.NameMap ProblemMeta)
  : IO Page := pure <| Page.dynamic "index.html" <| pure <| renderDoc <|
    base "Compfiles: Catalog of Math Problems Formalized in Lean"
    config (currentPage := .about) (includeHljs := true) <| [
      .p [] [
        "Welcome to Compfiles, a collaborative repository of olympiad-style"
        ++ " " ++ "math problems that have been formalized in the ",
        .a "https://leanprover-community.github.io" [cls "external"] "Lean",
        " theorem prover.",
      ],
      .p [] [
        "So far, ",
        .a (config.resolveRel ["all.html"]) [] [
          .b [] s!"{mds.size}", " problems and ",
          .b [] s!"{numProved}", " solutions",
        ],
        " have been formalized."
      ],
      .div [cls "toplevel-tables"] [
        compTable [
          imoContest.compRow config ["imo.html"] mds,
          usamoContest.compRow config ["usamo.html"] mds,
        ],
        tagTable tagFormalizedCounts tagSolvedCounts,
      ],
    ] ++ faq config
