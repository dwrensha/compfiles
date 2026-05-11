import Dashboard.Models.Contests
import Dashboard.Pages.ContestPage
import Dashboard.Pages.ProblemPage
import SSG.Html
import SSG.Tags

def preCmoProblemCounts : List (Nat × Nat) := [
  -- TODO: A-B version since 2015
  (2012, 4), (2011, 4), (2010, 4),
  (2009, 4), (2008, 3), (2007, 3), (2006, 3), (2005, 3),
  (2004, 3), (2003, 3), (2002, 3), (2001, 3), (2000, 3),
  (1999, 3), (1998, 3), (1997, 3), (1996, 4), (1995, 4),
  (1994, 4), (1993, 3), (1992, 3), (1991, 3), (1990, 3),
  (1989, 3), (1988, 3), (1987, 3), (1986, 3), (1985, 5),
  (1984, 5), (1983, 5),
]

public def preCmoContest : Contest Nat Nat := {
  fullName := "Pre-CMO"
  problems := fromCounts preCmoProblemCounts
  toName := fun year num ↦ s!"Compfiles.ChinaPre{year}P{num}".toName
  externalUrls := fun _ _ ↦ []
  desc := fun n ↦ [Html.p [] [
    "The China National High School Math League (Second Round) has included a total of ",
    Html.b [] s!"{n}", " problems."
  ]]
}

public def PreCmo.genAll (config : SConfig)
  (mds : Lean.NameMap ProblemMeta) : IO <| List Page := do
  let mut pages := []
  pages := pages ++ (← preCmoContest.generateProblems config mds)
  pages := (← preCmoContest.generate config
    "pre-cmo.html" .precmo mds (s!"{·}") (s!"P{·}")) :: pages
  return pages
