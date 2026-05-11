import Dashboard.Models.Contests
import Dashboard.Pages.ContestPage
import Dashboard.Pages.ProblemPage
import SSG.Html
import SSG.Tags

def cmoProblemCounts : List (Nat × Nat) := [
  (2025, 6),
  (2024, 6), (2023, 6), (2022, 6), (2021, 6), (2020, 6),
  (2019, 6), (2018, 6), (2017, 6), (2016, 6), (2015, 6),
  (2014, 6), (2013, 6), (2012, 6), (2011, 6), (2010, 6),
  (2009, 6), (2008, 6), (2007, 6), (2006, 6), (2005, 6),
  (2004, 6), (2003, 6), (2002, 6), (2001, 6), (2000, 6),
  (1999, 6), (1998, 6), (1997, 6), (1996, 6), (1995, 6),
  (1994, 6), (1993, 6), (1992, 6), (1991, 6), (1990, 6),
  (1989, 6), (1988, 6), (1987, 6), (1986, 6),
]

public def cmoContest : Contest Nat Nat := {
  fullName := "CMO"
  problems := fromCounts cmoProblemCounts
  toName := fun year num ↦ s!"Compfiles.Cmo{year}P{num}".toName
  externalUrls := fun _ _ ↦ []
  desc := fun n ↦ [Html.p [] [
    "The China Mathematical Olympiad (CMO) has included a total of ",
    Html.b [] s!"{n}", " problems."
  ]]
}

public def Cmo.genAll (config : SConfig)
  (mds : Lean.NameMap ProblemMeta) : IO <| List Page := do
  let mut pages := []
  pages := pages ++ (← cmoContest.generateProblems config mds)
  pages := (← cmoContest.generate config
    "cmo.html" .cmo mds (s!"{·}") (s!"P{·}")) :: pages
  return pages
