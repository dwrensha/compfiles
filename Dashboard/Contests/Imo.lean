import Dashboard.Models.Contests
import Dashboard.Pages.ContestPage
import Dashboard.Pages.ProblemPage
import SSG.Html
import SSG.Tags

def imoProblemCounts := [
  (2025, 6),
  (2024, 6), (2023, 6), (2022, 6), (2021, 6), (2020, 6),
  (2019, 6), (2018, 6), (2017, 6), (2016, 6), (2015, 6),
  (2014, 6), (2013, 6), (2012, 6), (2011, 6), (2010, 6),
  (2009, 6), (2008, 6), (2007, 6), (2006, 6), (2005, 6),
  (2004, 6), (2003, 6), (2002, 6), (2001, 6), (2000, 6),
  (1999, 6), (1998, 6), (1997, 6), (1996, 6), (1995, 6),
  (1994, 6), (1993, 6), (1992, 6), (1991, 6), (1990, 6),
  (1989, 6), (1988, 6), (1987, 6), (1986, 6), (1985, 6),
  (1984, 6), (1983, 6), (1982, 6), (1981, 6), --no contest in 1980
  (1979, 6), (1978, 6), (1977, 6), (1976, 6), (1975, 6),
  (1974, 6), (1973, 6), (1972, 6), (1971, 6), (1970, 6),
  (1969, 6), (1968, 6), (1967, 6), (1966, 6), (1965, 6),
  (1964, 6), (1963, 6), (1962, 7), (1961, 6), (1960, 7),
  (1959, 6)
]

def officialImoUrl (year : Nat) (_idx : Nat) : String :=
  s!"https://www.imo-official.org/assets/documents/problems/{year}/{year}_eng.pdf"

def aopsImoUrl (year : Nat) (idx : Nat) : String :=
  s!"https://artofproblemsolving.com/wiki/index.php/{year}_IMO_Problems/Problem_{idx}"

def scholesImoUrl (year : Nat) (idx : Nat) : String :=
  let year' := Substring.Raw.mk s!"{year}" ⟨2⟩ ⟨4⟩
  s!"https://prase.cz/kalva/imo/isoln/isoln{year'}{idx}.html"

def chenImoUrl (year : Nat) (_idx : Nat) : String :=
  s!"https://web.evanchen.cc/exams/IMO-{year}-notes.pdf"

def scannedPaperUrl (year : Nat) (idx : Nat) : Option String :=
  if year = 1971
  then if idx < 4
       then some "https://www.imo-register.org.uk/papers/1971-English-day1.jpeg"
       else some "https://www.imo-register.org.uk/papers/1971-English-day2.jpeg"
  else none

def allImoUrls (year : Nat) (idx : Nat) : List WriteupLink := Id.run do
  let mut result := [
    ⟨officialImoUrl year idx, "www.imo-official.org/problems"⟩,
    ⟨aopsImoUrl year idx, "Art of Problem Solving"⟩]
  if year ≤ 2003 then
    result := result ++ [⟨scholesImoUrl year idx, "John Scholes"⟩]
  if year ≥ 1997 ∧ year ≤ 2025 then
    result := result ++ [⟨chenImoUrl year idx, "Evan Chen"⟩]
  if let some url := scannedPaperUrl year idx then
    result := result ++ [⟨url, "scan of original paper"⟩]
  return result

public def imoContest : Contest Nat Nat := {
  fullName := "IMO"
  problems := fromCounts imoProblemCounts
  toName := fun year num => s!"Compfiles.Imo{year}P{num}".toName
  externalUrls := allImoUrls
  desc := fun n ↦ [Html.p [] [
    "Since 1959, the International Mathematical Olympiad has included a total of ",
    Html.b [] s!"{n}", " problems."
  ]]
}

public def Imo.genAll (config : SConfig)
  (mds : Lean.NameMap ProblemMeta) : IO <| List Page := do
  let mut pages := []
  pages := pages ++ (← imoContest.generateProblems config mds)
  pages := (← imoContest.generate config
    "imo.html" .imo mds (s!"{·}") (s!"P{·}")) :: pages
  return pages
