import Std.Data.RBMap.Basic
import Std.Data.String.Basic
import Std.Lean.Util.Path
import Std.Tactic.Lint
import Lean.Environment
import Mathlib.Data.String.Defs
import Lean.Meta.Basic

import ProblemExtraction

open Lean Core Elab Command Std.Tactic.Lint

def imoProblemCounts :=
  [(2023, 6), (2022, 6), (2021, 6), (2020, 6),
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
   (1959, 6)]

def totalImoProblemCount : Id Nat := do
  let mut result := 0
  for ⟨_, c⟩ in imoProblemCounts do
    result := result + c
  return result

def aopsImoUrl (year : Nat) (idx : Nat) : String :=
  s!"https://artofproblemsolving.com/wiki/index.php/{year}_IMO_Problems/Problem_{idx}"

def scholesImoUrl (year : Nat) (idx : Nat) : String :=
  let year' := Substring.mk s!"{year}" ⟨2⟩ ⟨4⟩
  s!"https://prase.cz/kalva/imo/isoln/isoln{year'}{idx}.html"

def chenImoUrl (year : Nat) (_idx : Nat) : String :=
  s!"https://web.evanchen.cc/exams/IMO-{year}-notes.pdf"

structure ExternalLink where
  url : String
  text : String

def allImoUrls (year : Nat) (idx : Nat) : List ExternalLink :=
  Id.run
  do let mut result := [⟨aopsImoUrl year idx, "Art of Problem Solving"⟩]
     if year ≤ 2003
     then result := result ++ [⟨scholesImoUrl year idx, "John Scholes"⟩]
     if year ≥ 1997 ∧ year ≤ 2023
     then result := result ++ [⟨chenImoUrl year idx, "Evan Chen"⟩]
     return result

-- If the problem is an Imo problem, return the year number and the problem number
def parseImoProblemId (probId : String) : Option (Nat × Nat) :=
  if probId.startsWith "Imo" ∧ probId.get ⟨3⟩ ∈ ['1', '2']
  then let ys := Substring.mk probId ⟨3⟩ ⟨7⟩
       let ns := Substring.mk probId ⟨8⟩ ⟨9⟩
       .some ⟨ys.toString.toNat!, ns.toString.toNat!⟩
  else .none

def isImoProblemId (probId : String) : Bool := (parseImoProblemId probId).isSome

def usamoProblemCounts :=
  [(2023, 5), (2022, 5), (2021, 5), (2020, 5),
   (2019, 5), (2018, 5), (2017, 5), (2016, 5), (2015, 5),
   (2014, 5), (2013, 5), (2012, 5), (2011, 5), (2010, 5),
   (2009, 5), (2008, 5), (2007, 5), (2006, 5), (2005, 5),
   (2004, 5), (2003, 5), (2002, 5), (2001, 5), (2000, 5),
   (1999, 5), (1998, 5), (1997, 5), (1996, 5), (1995, 5),
   (1994, 5), (1993, 5), (1992, 5), (1991, 5), (1990, 5),
   (1989, 5), (1988, 5), (1987, 5), (1986, 5), (1985, 5),
   (1984, 5), (1983, 5), (1982, 5), (1981, 5), (1980, 5),
   (1979, 5), (1978, 5), (1977, 5), (1976, 5), (1975, 5),
   (1974, 5), (1973, 5), (1972, 5)]

def totalUsamoProblemCount : Id Nat := do
  let mut result := 0
  for ⟨_, c⟩ in usamoProblemCounts do
    result := result + c
  return result

def aopsUsamoUrl (year : Nat) (idx : Nat) : String :=
  s!"https://artofproblemsolving.com/wiki/index.php/{year}_USAMO_Problems/Problem_{idx}"

def scholesUsamoUrl (year : Nat) (idx : Nat) : String :=
  let year' := Substring.mk s!"{year}" ⟨2⟩ ⟨4⟩
  s!"https://prase.cz/kalva/usa/usoln/usol{year'}{idx}.html"

def chenUsamoUrl (year : Nat) (_idx : Nat) : String :=
  s!"https://web.evanchen.cc/exams/USAMO-{year}-notes.pdf"

def allUsamoUrls (year : Nat) (idx : Nat) : List ExternalLink :=
  Id.run
  do let mut result := [⟨aopsUsamoUrl year idx, "Art of Problem Solving"⟩]
     if year ≤ 2003
     then result := result ++ [⟨scholesUsamoUrl year idx, "John Scholes"⟩]
     if year ≥ 1997 ∧ year ≤ 2023
     then result := result ++ [⟨chenUsamoUrl year idx, "Evan Chen"⟩]
     return result

-- If the problem is an Imo problem, return the year number and the problem number
def parseUsamoProblemId (probId : String) : Option (Nat × Nat) :=
  if probId.startsWith "Usa" ∧ probId.get ⟨3⟩ ∈ ['1', '2']
  then let ys := Substring.mk probId ⟨3⟩ ⟨7⟩
       let ns := Substring.mk probId ⟨8⟩ ⟨9⟩
       .some ⟨ys.toString.toNat!, ns.toString.toNat!⟩
  else .none

def isUsamoProblemId (probId : String) : Bool := (parseUsamoProblemId probId).isSome

def getWriteupLinks (probId : String) : List ExternalLink :=
  if let .some ⟨year, num⟩ := parseImoProblemId probId
  then allImoUrls year num
  else if let .some ⟨year, num⟩ := parseUsamoProblemId probId
  then allUsamoUrls year num
  else []

structure ProblemInfo where
  name : String
  informal : String
  metadata : ProblemExtraction.ProblemFileMetadata
  solutionUrl : String
  problemUrl : String
  proved : Bool

def problemTagClass (tag : ProblemExtraction.ProblemTag) : String :=
  (ToString.toString tag).replace " " "-"

def sortProblems (infos : List ProblemInfo) : List ProblemInfo :=
  let ⟨imos, rest⟩ := infos.partition (·.name.startsWith "Imo")
  let ⟨usamos, rest⟩ := rest.partition (·.name.startsWith "Usa")
  (imos.toArray.qsort (fun a1 a2 ↦ a1.name < a2.name)).toList
   ++
  (usamos.toArray.qsort (fun a1 a2 ↦ a1.name < a2.name)).toList
   ++ (rest.toArray.qsort (fun a1 a2 ↦ a1.name < a2.name)).toList

def htmlEscapeAux (racc : List Char) : List Char → String
| [] => String.mk racc.reverse
| '&'::cs => htmlEscapeAux (("&amp;".data.reverse)++racc) cs
| '<'::cs => htmlEscapeAux (("&lt;".data.reverse)++racc) cs
| '>'::cs => htmlEscapeAux (("&gt;".data.reverse)++racc) cs
| '\"'::cs => htmlEscapeAux (("&quot;".data.reverse)++racc) cs
-- TODO other things that need escaping
-- https://developer.mozilla.org/en-US/docs/Glossary/Entity#reserved_characters
| c::cs => htmlEscapeAux (c::racc) cs

def htmlEscape (s : String) : String :=
  htmlEscapeAux [] s.data

def olean_path_to_github_url (path: String) : String :=
  let pfx := "./.lake/build/lib/"
  let sfx := ".olean"
  assert!(pfx.isPrefixOf path)
  assert!(sfx.data.isSuffixOf path.data)
  "https://github.com/dwrensha/compfiles/blob/main/" ++
    ((path.stripPrefix pfx).stripSuffix sfx) ++ ".lean"

def extractModuleDoc (env : Environment) (m : Name) : String :=
  match Lean.getModuleDoc? env m with
  | some mda => String.join (mda.toList.map ModuleDoc.doc)
  | _ => ""

def getBaseUrl : IO String := do
  let cwd ← IO.currentDir
  pure ((← IO.getEnv "GITHUB_PAGES_BASEURL").getD s!"file://{cwd}/_site/")

def htmlHeader (title : String) : IO String := do
  let baseurl ← getBaseUrl
  pure <|
    "<!DOCTYPE html><html><head>" ++
    "<meta name=\"viewport\" content=\"width=device-width\">" ++
    s!"<link rel=\"stylesheet\" type=\"text/css\" href=\"{baseurl}main.css\" >" ++
    s!"<title>{title}</title>" ++
    "</head>\n<body>"

def topbar (currentPage : String) : IO String := do
  let baseurl ← getBaseUrl
  let commit_sha := ((← IO.getEnv "GITHUB_SHA").getD "GITHUB_SHA_env_var_not_found")
  let commit_url :=
        s!"https://github.com/dwrensha/compfiles/commit/{commit_sha}"
  let mut result :=
    "<h2>" ++
    "<a href=\"https://github.com/dwrensha/compfiles\">" ++
    "Compfiles</a>: Catalog Of Math Problems Formalized In Lean.</h2>" ++
    s!"<p>(Generated by commit <a href=\"{commit_url}\">{commit_sha}</a>.)</p>"

  let all :=
    if currentPage == "all"
    then "<span class=\"active\">All</span>"
    else s!"<span class=\"inactive\"><a href=\"{baseurl}index.html\">All</a></span>"
  let imo :=
    if currentPage == "imo"
    then "<span class=\"active\">IMO</span>"
    else s!"<span class=\"inactive\"><a href=\"{baseurl}imo.html\">IMO</a></span>"
  let usamo :=
    if currentPage == "usamo"
    then "<span class=\"active\">USAMO</span>"
    else s!"<span class=\"inactive\"><a href=\"{baseurl}usamo.html\">USAMO</a></span>"

  result := result ++
    s!"<div class=\"navbar\">{all}{imo}{usamo}</div>"
  return result

unsafe def main (_args : List String) : IO Unit := do
  IO.FS.createDirAll "_site"
  IO.FS.createDirAll "_site/problems"
  IO.FS.writeFile "_site/main.css" (←IO.FS.readFile "scripts/main.css")

  let module := `Compfiles
  searchPathRef.set compile_time_search_path%

  withImportModules #[{module}] {} (trustLevel := 1024) fun env =>
    let ctx := {fileName := "", fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      let mst ← ProblemExtraction.extractProblems
      let mds ← ProblemExtraction.extractMetadata

      let mut infos : List ProblemInfo := []
      for ⟨m, problem_src⟩ in mst do
          let p ← findOLean m
          let solutionUrl := olean_path_to_github_url p.toString
          IO.println s!"MODULE: {m}"
          let problemFile := s!"problems/{m}.html"
          let problemUrl := s!"{←getBaseUrl}{problemFile}"
          let homeUrl := s!"{←getBaseUrl}index.html"

          let mut proved := true
          let decls ← getDeclsInPackage m
          for d in decls do
            let c ← getConstInfo d
            match c.value? with
            | none => pure ()
            | some v => do
                 if v.hasSorry then proved := false

          let metadata := (mds.find? m).getD {}
          let probId := m.toString.stripPrefix "Compfiles."
          infos := ⟨probId,
                    extractModuleDoc env m,
                    metadata,
                    solutionUrl, problemUrl, proved⟩ :: infos

          let h ← IO.FS.Handle.mk ("_site/" ++ problemFile) IO.FS.Mode.write
          h.putStrLn <| ←htmlHeader m.toString
          h.putStrLn "<pre class=\"problem\">"
          h.putStr (htmlEscape problem_src)
          h.putStrLn "</pre>"
          if proved
          then
            let authors :=
              if metadata.authors.isEmpty then "" else
              s!" written by {" and ".intercalate metadata.authors}"
            h.putStrLn
              s!"<p>This problem <a href=\"{solutionUrl}\">has a complete formalized solution</a>{authors}.</p>"
          else
            h.putStrLn
              s!"<p>This problem <a href=\"{solutionUrl}\">does not yet have a complete formalized solution</a>.</p>"
          if let .some url := metadata.importedFrom
          then
            -- Make github urls a little nicer to look at.
            let text :=
              if url.startsWith "https://github.com/"
              then let rest := url.stripPrefix "https://github.com/"
                   match rest.splitOn "/" with
                   | _ns :: repo :: _blob :: _branch :: rest =>
                      "/".intercalate (repo :: rest)
                   | _ => url
              else url
            h.putStrLn s!"<p>The solution was imported from <a href=\"{url}\">{text}</a>.</p>"
          let writeupLinks := getWriteupLinks probId
          if writeupLinks.length > 0
          then h.putStrLn s!"<div>Informal writeups:<ul class=\"writeups\">"
               for ⟨url, text⟩ in writeupLinks do
                 h.putStrLn s!"<li><a href=\"{url}\">{text}</a></li>"
               h.putStrLn s!"</ul></div>"

          h.putStrLn "<hr>"
          h.putStrLn "<div class=\"footer-row\">"
          h.putStrLn s!"<a class=\"home-link\" href=\"{homeUrl}\">Compfiles</a>"
          h.putStrLn "</div>"
          h.putStrLn "</body></html>"
          h.flush

      -- now write the main index.html
      let num_proved := (infos.filter (·.proved)).length

      let h ← IO.FS.Handle.mk "_site/index.html" IO.FS.Mode.write
      h.putStrLn <| ←htmlHeader "Compfiles: Catalog of Math Problems Formalized in Lean"
      h.putStrLn <| ← topbar "all"
      h.putStr s!"<p>{num_proved} / {infos.length} formalized problems have been solved.<p>"
      h.putStr "<table class=\"problems\">"
      h.putStr "<thead><tr><th>problem</th><th>solved?</th><th>tags</th></tr></thead>"
      h.putStr "<tbody>"
      let infos' := sortProblems infos
      let mut infomap := Std.mkRBMap String ProblemInfo Ord.compare
      let mut imoSolvedCount := 0
      let mut imoFormalizedCount := 0

      let mut usamoSolvedCount := 0
      let mut usamoFormalizedCount := 0


      for info in infos' do
        infomap := infomap.insert info.name info
        if isImoProblemId info.name then
          imoFormalizedCount := imoFormalizedCount + 1
          if info.proved then
            imoSolvedCount := imoSolvedCount + 1
          pure ()
        if isUsamoProblemId info.name then
          usamoFormalizedCount := usamoFormalizedCount + 1
          if info.proved then
            usamoSolvedCount := usamoSolvedCount + 1
          pure ()
        h.putStr s!"<tr>"

        -- problem name
        h.putStr s!"<td title=\"{htmlEscape info.informal}\" class=\"problem-page-link\">"
        h.putStr s!"<a href=\"{info.problemUrl}\">{info.name}</a>"
        h.putStr "</td>"

        -- solved or not?
        h.putStr "<td class=\"solved-col\">"
        h.putStr s!"<a href=\"{info.solutionUrl}\">"
        if info.proved then
          h.putStr s!"<span title=\"complete solution\">✅</span>"
        else
          h.putStr s!"<span title=\"incomplete or missing solution\">❌</span>"
        h.putStr "</a>"
        h.putStr "</td>"

        -- tags
        h.putStr "<td class=\"tags-col\">"
        for tg in info.metadata.tags do
          h.putStr s!"<span class=\"problem-tag {problemTagClass tg}\">{tg}</span>"
        h.putStr "</td>"
        h.putStr "</tr>"
      h.putStr "</tbody>"
      h.putStr "</table>"
      h.putStr "</body></html>"

      let h ← IO.FS.Handle.mk "_site/imo.html" IO.FS.Mode.write
      h.putStrLn <| ←htmlHeader "Compfiles: Catalog of Math Problems Formalized in Lean"
      h.putStrLn <| ← topbar "imo"
      h.putStrLn <| s!"<p>Since 1959, the International Mathematical Olympiad has included  a total of <b>{totalImoProblemCount}</b> problems.</p>"
      let formalizedPercent : Float := 100.0 *
        (OfNat.ofNat imoFormalizedCount) / (OfNat.ofNat totalImoProblemCount)
      h.putStrLn <| s!"<p><b>{imoFormalizedCount}</b> problems have been formalized ({formalizedPercent}%).</p>"
      let solvedPercent : Float := 100.0 *
        (OfNat.ofNat imoSolvedCount) / (OfNat.ofNat totalImoProblemCount)
      h.putStrLn <| s!"<p><b>{imoSolvedCount}</b> problems have complete formalized solutions ({solvedPercent}%).</p>"
      h.putStr "<table class=\"full-problem-grid\">"
      for ⟨year, count⟩ in imoProblemCounts do
        h.putStr s!"<tr><td class=\"year\">{year}</td>"
        for ii in List.range count do
          let idx := ii + 1
          let name := s!"Imo{year}P{idx}"
          let ⟨url, cls⟩ ← match infomap.find? name with
          | .some info =>
            let url := s!"problems/Compfiles.{name}.html"
            let cls := if info.proved then "proved" else "formalized"
            pure (url, cls)
          | .none =>
            pure (aopsImoUrl year idx, "todo")

          h.putStr s!"<td class=\"{cls}\"><a href=\"{url}\">P{idx}</a></td>"
          pure ()
        h.putStrLn "</tr>"
      h.putStr "</table>"

      h.putStr "</body></html>"
      pure ()

      let h ← IO.FS.Handle.mk "_site/usamo.html" IO.FS.Mode.write
      h.putStrLn <| ←htmlHeader "Compfiles: Catalog of Math Problems Formalized in Lean"
      h.putStrLn <| ← topbar "usamo"
      h.putStrLn <| s!"<p>Since 1972, the USA Mathematical Olympiad has included a total of <b>{totalUsamoProblemCount}</b> problems.</p>"
      let formalizedPercent : Float := 100.0 *
        (OfNat.ofNat usamoFormalizedCount) / (OfNat.ofNat totalUsamoProblemCount)
      h.putStrLn <| s!"<p><b>{usamoFormalizedCount}</b> problems have been formalized ({formalizedPercent}%).</p>"
      let solvedPercent : Float := 100.0 *
        (OfNat.ofNat usamoSolvedCount) / (OfNat.ofNat totalUsamoProblemCount)
      h.putStrLn <| s!"<p><b>{usamoSolvedCount}</b> problems have complete formalized solutions ({solvedPercent}%).</p>"
      h.putStr "<table class=\"full-problem-grid\">"
      for ⟨year, count⟩ in usamoProblemCounts do
        h.putStr s!"<tr><td class=\"year\">{year}</td>"
        for ii in List.range count do
          let idx := ii + 1
          let name := s!"Usa{year}P{idx}"
          let ⟨url, cls⟩ ← match infomap.find? name with
          | .some info =>
            let url := s!"problems/Compfiles.{name}.html"
            let cls := if info.proved then "proved" else "formalized"
            pure (url, cls)
          | .none =>
            pure (aopsUsamoUrl year idx, "todo")

          h.putStr s!"<td class=\"{cls}\"><a href=\"{url}\">P{idx}</a></td>"
          pure ()
        h.putStrLn "</tr>"
      h.putStr "</table>"

      h.putStr "</body></html>"
      pure ()
