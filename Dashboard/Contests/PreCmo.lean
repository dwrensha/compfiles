import Dashboard.Models.Contests
import Dashboard.Pages.ContestPage
import Dashboard.Pages.ProblemPage
import SSG.Html
import SSG.Tags

inductive Schedule where
| mono (count : Nat)
| ab (aCount : Nat) (bCount : Nat)
/-- COVID-19 pandemic -/
| p2021
/-- COVID-19 pandemic -/
| p2022

def preCmoProblemCounts : List (Nat × Schedule) := [
  (2025, .ab 4 4),
  (2024, .ab 4 4), (2023, .ab 4 4), (2022, .p2022), (2021, .p2021), (2020, .ab 4 4),
  (2019, .ab 4 4), (2018, .ab 4 4), (2017, .ab 4 4), (2016, .mono 4), (2015, .mono 4),
  (2014, .mono 4), (2013, .mono 4), (2012, .mono 4), (2011, .mono 4), (2010, .mono 4),
  (2009, .mono 4), (2008, .mono 3), (2007, .mono 3), (2006, .mono 3), (2005, .mono 3),
  (2004, .mono 3), (2003, .mono 3), (2002, .mono 3), (2001, .mono 3), (2000, .mono 3),
  (1999, .mono 3), (1998, .mono 3), (1997, .mono 3), (1996, .mono 4), (1995, .mono 4),
  (1994, .mono 4), (1993, .mono 3), (1992, .mono 3), (1991, .mono 3), (1990, .mono 3),
  (1989, .mono 3), (1988, .mono 3), (1987, .mono 3), (1986, .mono 3), (1985, .mono 5),
  (1984, .mono 5), (1983, .mono 5),
]

structure Round where
  year : Nat
  id : Option String
deriving Ord

instance : ToString Round where
  toString := fun s ↦ s!"{s.year}" ++ (match s.id with | .some s => s | .none => "")


def fromSchedules (counts : List (Nat × Schedule)) : List (Round × Nat) :=
  counts.flatMap fun ⟨year, s⟩ => match s with
  | .mono c => (List.range c).map (⟨year, .none⟩, · + 1)
  | .ab a b => (List.range a).map (⟨year, .some "A"⟩, · + 1)
    ++ (List.range b).map (⟨year, .some "B"⟩, · + 1)
  | .p2021 => (List.range 4).map (⟨year, .some "A1"⟩, · + 1)
    ++ (List.range 4).map (⟨year, .some "A2"⟩, · + 1)
    ++ (List.range 4).map (⟨year, .some "B"⟩, · + 1)
  | .p2022 => (List.range 4).map (⟨year, .some "A"⟩, · + 1)
    ++ (List.range 4).map (⟨year, .some "A1"⟩, · + 1)
    ++ (List.range 4).map (⟨year, .some "A2"⟩, · + 1)
    ++ (List.range 4).map (⟨year, .some "B"⟩, · + 1)
    ++ (List.range 4).map (⟨year, .some "B1"⟩, · + 1)

public def preCmoContest : Contest Round Nat := {
  fullName := "Pre-CMO"
  problems := fromSchedules preCmoProblemCounts
  toName := fun year sub ↦ s!"Compfiles.ChinaPre{year}P{sub}".toName
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
