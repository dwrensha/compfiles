import Dashboard.Models.Contests
import Dashboard.Pages.ContestPage
import Dashboard.Pages.ProblemPage
import SSG.Html
import SSG.Tags

def usamoProblemCounts := [
  (2026, 6), (2025, 6),
  (2024, 6), (2023, 6), (2022, 6), (2021, 6), (2020, 6),
  (2019, 6), (2018, 6), (2017, 6), (2016, 6), (2015, 6),
  (2014, 6), (2013, 6), (2012, 6), (2011, 6), (2010, 6),
  (2009, 6), (2008, 6), (2007, 6), (2006, 6), (2005, 6),
  (2004, 6), (2003, 6), (2002, 6), (2001, 6), (2000, 6),
  (1999, 6), (1998, 6), (1997, 6), (1996, 6), (1995, 5),
  (1994, 5), (1993, 5), (1992, 5), (1991, 5), (1990, 5),
  (1989, 5), (1988, 5), (1987, 5), (1986, 5), (1985, 5),
  (1984, 5), (1983, 5), (1982, 5), (1981, 5), (1980, 5),
  (1979, 5), (1978, 5), (1977, 5), (1976, 5), (1975, 5),
  (1974, 5), (1973, 5), (1972, 5)
]

def aopsUsamoUrl (year : Nat) (idx : Nat) : String :=
  s!"https://artofproblemsolving.com/wiki/index.php/{year}_USAMO_Problems/Problem_{idx}"

def scholesUsamoUrl (year : Nat) (idx : Nat) : String :=
  let year' := Substring.Raw.mk s!"{year}" ⟨2⟩ ⟨4⟩
  s!"https://prase.cz/kalva/usa/usoln/usol{year'}{idx}.html"

def chenUsamoUrl (year : Nat) (_idx : Nat) : String :=
  s!"https://web.evanchen.cc/exams/USAMO-{year}-notes.pdf"

def allUsamoUrls (year : Nat) (idx : Nat) : List WriteupLink := Id.run do
  let mut result := [⟨aopsUsamoUrl year idx, "Art of Problem Solving"⟩]
  if year ≤ 2003 ∧ year ≠ 1989 /- 1989 is weirdly missing -/ then
    result := result ++ [⟨scholesUsamoUrl year idx, "John Scholes"⟩]
  if year ≥ 1996 ∧ year ≤ 2025 then
    result := result ++ [⟨chenUsamoUrl year idx, "Evan Chen"⟩]
  return result

public def usamoContest : Contest Nat Nat := {
  fullName := "USAMO"
  problems := fromCounts usamoProblemCounts
  toName := fun year num => s!"Compfiles.Usa{year}P{num}".toName
  externalUrls := allUsamoUrls
  desc := fun n ↦ [Html.p [] [
    "Since 1972, the USA Mathematical Olympiad has included a total of ",
    Html.b [] s!"{n}", " problems."
  ]]
}

public def Usamo.genAll (config : SConfig)
  (mds : Lean.NameMap ProblemMeta) : IO <| List Page := do
  let mut pages := []
  pages := pages ++ (← usamoContest.generateProblems config mds)
  pages := (← usamoContest.generate config
    "usamo.html" .usamo mds (s!"{·}") (s!"P{·}")) :: pages
  return pages
