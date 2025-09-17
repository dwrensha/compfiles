import Batteries.Data.RBMap.Basic
import Batteries.Data.String.Basic
import Batteries.Tactic.Lint
import Lean.Environment
import Mathlib.Data.String.Defs
import Lean.Meta.Basic

import ProblemExtraction

set_option linter.style.longLine false

open Lean Core Elab Command Batteries.Tactic.Lint

def imoProblemCounts :=
  [(2025, 6),
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
   (1959, 6)]

def totalImoProblemCount : Id Nat := do
  let mut result := 0
  for ⟨_, c⟩ in imoProblemCounts do
    result := result + c
  return result

def officialImoUrl (year : Nat) (_idx : Nat) : String :=
  s!"https://www.imo-official.org/problems/{year}/eng.pdf"

def aopsImoUrl (year : Nat) (idx : Nat) : String :=
  s!"https://artofproblemsolving.com/wiki/index.php/{year}_IMO_Problems/Problem_{idx}"

def scholesImoUrl (year : Nat) (idx : Nat) : String :=
  let year' := Substring.mk s!"{year}" ⟨2⟩ ⟨4⟩
  s!"https://prase.cz/kalva/imo/isoln/isoln{year'}{idx}.html"

def chenImoUrl (year : Nat) (_idx : Nat) : String :=
  s!"https://web.evanchen.cc/exams/IMO-{year}-notes.pdf"

def scannedPaperUrl (year : Nat) (idx : Nat) : Option String :=
  if year = 1971
  then if idx < 4
       then some "https://www.imo-register.org.uk/papers/1971-English-day1.jpeg"
       else some "https://www.imo-register.org.uk/papers/1971-English-day2.jpeg"
  else none

structure WriteupLink where
  url : String
  text : String

def allImoUrls (year : Nat) (idx : Nat) : List WriteupLink :=
  Id.run
  do let mut result := [
         ⟨officialImoUrl year idx, "www.imo-official.org/problems"⟩,
         ⟨aopsImoUrl year idx, "Art of Problem Solving"⟩]
     if year ≤ 2003
     then result := result ++ [⟨scholesImoUrl year idx, "John Scholes"⟩]
     if year ≥ 1997 ∧ year ≤ 2025
     then result := result ++ [⟨chenImoUrl year idx, "Evan Chen"⟩]
     if let some url := scannedPaperUrl year idx
     then result := result ++ [⟨url, "scan of original paper"⟩]

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
  [(2025, 6),
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

def allUsamoUrls (year : Nat) (idx : Nat) : List WriteupLink :=
  Id.run
  do let mut result := [⟨aopsUsamoUrl year idx, "Art of Problem Solving"⟩]
     if year ≤ 2003 ∧ year ≠ 1989 /- 1989 is weirdly missing -/
     then result := result ++ [⟨scholesUsamoUrl year idx, "John Scholes"⟩]
     if year ≥ 1996 ∧ year ≤ 2025
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

def getWriteupLinks (probId : String) : List WriteupLink :=
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

def stringifyPercent (p : Float) : String :=
  let s1 := s!"{p * 100}"
  let pos := s1.find (fun c ↦ c = '.')
  if pos = s1.endPos then
    s1 ++ "%"
  else
    let p1 := pos + ⟨3⟩
    let s2 := Substring.mk s1 0 p1
    s2.toString ++ "%"

def olean_path_to_github_url (path : System.FilePath) : IO String := do
  let path_components := path.components.dropWhile (· = ".")
  let cwd ← IO.currentDir
  let relative_olean_path_components := path_components.drop (cwd.components.length)
  assert!(relative_olean_path_components.take 4 = [".lake", "build", "lib", "lean"])
  let sfx := ".olean"
  let path' := (System.mkFilePath (relative_olean_path_components.drop 4)).toString
  assert!(sfx.data.isSuffixOf path'.data)
  return "https://github.com/dwrensha/compfiles/blob/main/" ++
            (path'.stripSuffix sfx) ++ ".lean"

def extractModuleDoc (env : Environment) (m : Name) : String :=
  match Lean.getModuleDoc? env m with
  | some mda => String.join (mda.toList.map ModuleDoc.doc)
  | _ => ""

def getBaseUrl : IO String := do
  let cwd ← IO.currentDir
  pure ((← IO.getEnv "GITHUB_PAGES_BASEURL").getD s!"file://{cwd}/_site/")

def htmlHeader (title : String) (includeHljs : Bool := false) : IO String := do
  let baseurl ← getBaseUrl
  pure <|
    "<!DOCTYPE html><html><head>" ++
    "<meta name=\"viewport\" content=\"width=device-width\">" ++
    s!"<link rel=\"stylesheet\" type=\"text/css\" href=\"{baseurl}main.css\" >" ++
    s!"<link rel=\"icon\" type=\"image/ico\" href=\"{baseurl}favicon.ico\">" ++
    s!"<link rel=\"apple-touch-icon\" href=\"{baseurl}apple-touch-icon.png\">" ++
    s!"<meta property=\"og:image\" content=\"{baseurl}og-preview.png\">" ++
    s!"<title>{title}</title>" ++
    (if includeHljs
     then
       s!"<link rel=\"stylesheet\" type=\"text/css\" href=\"{baseurl}docco.css\">" ++
       s!"<script src=\"{baseurl}highlight.min.js\"></script>" ++
       s!"<script src=\"{baseurl}lean.js\"></script>" ++
       "<script>hljs.highlightAll();</script>"
     else "") ++
    "</head>\n<body>"

def footer : IO String := do
  let commit_sha := ((← IO.getEnv "GITHUB_SHA").getD "GITHUB_SHA_env_var_not_found")
  let commit_url :=
        s!"https://github.com/dwrensha/compfiles/commit/{commit_sha}"

  return "<hr><div class=\"footer\">" ++
      s!"Generated by commit <a class=\"external\" href=\"{commit_url}\">{commit_sha}</a>.</div>"

def topbar (currentPage : String) : IO String := do
  let baseurl ← getBaseUrl
  let mut result :=
    "<h2>" ++
    "<a class=\"external\" href=\"https://github.com/dwrensha/compfiles\">" ++
    "Compfiles</a>: Catalog Of Math Problems Formalized In Lean</h2>"

  let about :=
    if currentPage == "about"
    then "<span class=\"active\">About</span>"
    else s!"<span class=\"inactive\"><a href=\"{baseurl}index.html\">About</a></span>"
  let imo :=
    if currentPage == "imo"
    then "<span class=\"active\">IMO</span>"
    else s!"<span class=\"inactive\"><a href=\"{baseurl}imo.html\">IMO</a></span>"
  let usamo :=
    if currentPage == "usamo"
    then "<span class=\"active\">USAMO</span>"
    else s!"<span class=\"inactive\"><a href=\"{baseurl}usamo.html\">USAMO</a></span>"
  let all :=
    if currentPage == "all"
    then "<span class=\"active\">All</span>"
    else s!"<span class=\"inactive\"><a href=\"{baseurl}all.html\">All</a></span>"


  result := result ++
    s!"<div class=\"navbar\">{about}{imo}{usamo}{all}</div>"
  return result

def generateProblemStubFile (path : String) (probId : String) : IO Unit := do
  let h ← IO.FS.Handle.mk ("_site/" ++ path) IO.FS.Mode.write
  h.putStrLn <| ←htmlHeader ("Compfiles." ++ probId)
  h.putStrLn <| ← topbar "none"
  h.putStrLn s!"<h2>{probId}</h2>"
  h.putStrLn s!"<p>This problem has not been formalized yet!</p>"
  h.putStrLn "<p>To add a formalization of it, submit a pull request to the"
  h.putStrLn "<a class=\"external\" href=\"https://github.com/dwrensha/compfiles\">Compfiles Github repository</a>."
  h.putStrLn "</p>"

  let writeupLinks := getWriteupLinks probId
  if writeupLinks.length > 0
  then h.putStrLn s!"<div>External resources:<ul class=\"writeups\">"
       for ⟨url, text⟩ in writeupLinks do
         h.putStrLn s!"<li><a class=\"external\" href=\"{url}\">{text}</a></li>"
       h.putStrLn s!"</ul></div>"

  pure ()

def faq (h : IO.FS.Handle) : IO Unit := do
  h.putStrLn "<h3>Frequently Asked Questions</h3>"
  h.putStrLn "<h4>Why are you doing this?</h4>"
  h.putStr "<ul><li>It's a fun way to learn about math and mechanized reasoning!</li>"
  h.putStr "<li>It uncovers missing pieces of theory that ought to be in "
  h.putStr "<a class=\"external\" href=\"https://github.com/leanprover-community/mathlib4\">Mathlib</a>. "
  h.putStr "See for example Joseph Myers's "
  h.putStr "<a class=\"external\" href=\"https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry/near/321396912\">"
  h.putStr "Euclidean geometry TODO list"
  h.putStr "</a>.</li>"
  h.putStr "<li>It's a (small) first step toward solving the <a class=\"external\" href=\"https://imo-grand-challenge.github.io/\">"
  h.putStr "IMO Grand Challenge</a>."
  h.putStr "</li></ul>"
  h.putStrLn "<h4>Why is Compfiles a separate project when <a class=\"external\" href=\"https://github.com/leanprover-community/mathlib4/tree/master/Archive/Imo\">Mathlib/Archive/Imo</a> already exists?</h4>"
  h.putStr "<p>We want to minimize the burden that we place on Mathlib's maintainers and infrastructure. "
  h.putStr "Mathlib is a large enough monolith already. "
  h.putStr "Since Mathlib and Compfiles are both open source under the "
  h.putStr "Apache-2.0 license, it should be straightforward to "
  h.putStr "move code back and forth between them, if desired.</p>"

  h.putStrLn "<h4>How does Compfiles compare to <a class=\"external\" href=\"https://github.com/openai/miniF2F\">MiniF2F</a>?</h4>"
  h.putStr "<p>MiniF2F is a static benchmark for machine learning, with 488 math problems formalized in multiple languages (Lean, Metamath, Isabelle, and HOL Light) including a relatively small number of formalized solutions. "
  h.putStr "Compfiles is a continually-growing archive of math problems formalized in Lean, with emphasis placed on complete formalized solutions.</p>"

  h.putStrLn "<h4>How does Compfiles encode problems that ask for data values to be determined?</h4>"
  h.putStr "<p>We have special <code>determine</code> command to mark such data. "
  h.putStr s!"You can see it in action for Imo2015P5 <a href=\"https://github.com/dwrensha/compfiles/blob/16ce9a86e9e1c147482b264a6bbdbd4cd605a93e/Compfiles/Imo2015P5.lean#L25\">in the source code</a> and <a href=\"{←getBaseUrl}problems/Compfiles.Imo2015P5.html\">on the rendered webpage</a>, "
  h.putStr "and you can see its definition <a href=\"https://github.com/dwrensha/compfiles/blob/16ce9a86e9e1c147482b264a6bbdbd4cd605a93e/ProblemExtraction.lean#L245-L252\">here</a>.</p>"

  h.putStrLn "<h4>I noticed an error on this website. How do I report it?</h4>"
  h.putStr "<p>Please open an issue <a class=\"external\" href=\"https://github.com/dwrensha/compfiles/issues\">on Github</a>.</p>"

set_option maxRecDepth 2000 in
unsafe def main (_args : List String) : IO Unit := do
  IO.FS.createDirAll "_site"
  IO.FS.createDirAll "_site/problems"
  IO.FS.writeFile "_site/main.css" (←IO.FS.readFile "assets/main.css")
  IO.FS.writeBinFile "_site/favicon.ico" (←IO.FS.readBinFile "assets/favicon.ico")
  IO.FS.writeBinFile "_site/apple-touch-icon.png"
    (←IO.FS.readBinFile "assets/apple-touch-icon.png")
  IO.FS.writeBinFile "_site/og-preview.png"
    (←IO.FS.readBinFile "assets/og-preview.png")
  IO.FS.writeFile "_site/highlight.min.js" (←IO.FS.readFile "assets/highlight.min.js")
  IO.FS.writeFile "_site/docco.css" (←IO.FS.readFile "assets/docco.css")
  IO.FS.writeFile "_site/lean.js" (←IO.FS.readFile "assets/lean.js")

  let module := `Compfiles
  initSearchPath (← findSysroot)

  Lean.enableInitializersExecution
  let env ← importModules #[{module}] {} (trustLevel := 1024) #[] True True
  let ctx := {fileName := "", fileMap := default}
  let state := {env}
  Prod.fst <$> (CoreM.toIO · ctx state) do
    let mst ← ProblemExtraction.extractProblems
    let sols ← ProblemExtraction.extractSolutions
    let mds ← ProblemExtraction.extractMetadata

    let mut infos : List ProblemInfo := []
    for ⟨m, problem_src⟩ in mst do
      let p ← findOLean m
      let solutionUrl := ← olean_path_to_github_url p.normalize
      IO.println s!"MODULE: {m}"
      let problemFile := s!"problems/{m}.html"
      let rawProblemFile := s!"problems/{m}.lean"
      let problemUrl := s!"{←getBaseUrl}{problemFile}"
      let rawProblemUrl := s!"{←getBaseUrl}{rawProblemFile}"

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
      h.putStrLn <| ←htmlHeader m.toString (includeHljs := true)
      h.putStrLn <| ← topbar "none"
      h.putStrLn s!"<h2>{probId}</h2>"

      h.putStrLn "<pre class=\"problem\"><code class=\"language-lean\">"
      h.putStr (htmlEscape problem_src)
      h.putStrLn "</code></pre>"
      if !metadata.authors.isEmpty then
        h.putStrLn s!"<p class='authors'>File author(s): {", ".intercalate metadata.authors}</p>"
      if proved
      then
        h.putStrLn
          s!"<p>This problem <a class=\"external\" href=\"{solutionUrl}\">has a complete formalized solution</a>.</p>"
      else
        h.putStrLn
          s!"<p>This problem <a class=\"external\" href=\"{solutionUrl}\">does not yet have a complete formalized solution</a>.</p>"
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
        h.putStrLn s!"<p>The solution was imported from <a class=\"external\" href=\"{url}\">{text}</a>.</p>"

      let hraw ← IO.FS.Handle.mk ("_site/" ++ rawProblemFile) IO.FS.Mode.write
      hraw.putStr s!"{metadata.copyrightHeader}{problem_src}"

      let rawProblemLiveUrl := s!"https://live.lean-lang.org/#url={System.Uri.escapeUri rawProblemUrl}"

      h.putStrLn s!"<div>Open with the in-brower editor at live.lean-lang.org:"
      h.putStr s!"<ul class=\"live-links\"><li><a href=\"{rawProblemLiveUrl}\">problem statement only</a></li>"
      let soldesc := if proved then "complete solution" else "in-progress solution"
      if let some sol_src := sols.find? m then
        let rawSolFile := s!"problems/{m}.sol.lean"
        let rawSolUrl := s!"{←getBaseUrl}{rawSolFile}"
        let hraw ← IO.FS.Handle.mk ("_site/" ++ rawSolFile) IO.FS.Mode.write
        hraw.putStr s!"{metadata.copyrightHeader}{sol_src}"
        let rawSolLiveUrl := s!"https://live.lean-lang.org/#url={System.Uri.escapeUri rawSolUrl}"
        h.putStr s!"<li><a href=\"{rawSolLiveUrl}\">{soldesc}</a></li>"
      h.putStrLn "</ul></div>"

      let writeupLinks := getWriteupLinks probId
      if writeupLinks.length > 0
      then h.putStrLn s!"<div>External resources:<ul class=\"writeups\">"
           for ⟨url, text⟩ in writeupLinks do
             h.putStrLn s!"<li><a class=\"external\" href=\"{url}\">{text}</a></li>"
           h.putStrLn s!"</ul></div>"

      h.putStrLn (←footer)
      h.putStrLn "</body></html>"
      h.flush

    let mut tag_formalized_counts : Array Nat := Array.mk [0,0,0,0,0]
    let mut tag_solved_counts : Array Nat := Array.mk [0,0,0,0,0]

    -- now write all.html
    let num_proved := (infos.filter (·.proved)).length

    let h ← IO.FS.Handle.mk "_site/all.html" IO.FS.Mode.write
    h.putStrLn <| ←htmlHeader "Compfiles: Catalog of Math Problems Formalized in Lean"
    h.putStrLn <| ← topbar "all"
    h.putStrLn <| s!"<p><b>{infos.length}</b> problems have been formalized.</p>"
    h.putStrLn <| s!"<p><b>{num_proved}</b> problems have complete formalized solutions.</p>"
    h.putStr "<table class=\"problems\">"
    h.putStr "<thead><tr><th>problem</th><th>solved?</th><th>tags</th></tr></thead>"
    h.putStr "<tbody>"
    let infos' := sortProblems infos
    let mut infomap := Batteries.mkRBMap String ProblemInfo Ord.compare
    let mut imoSolvedCount := 0
    let mut imoFormalizedCount := 0

    let mut usamoSolvedCount := 0
    let mut usamoFormalizedCount := 0

    for info in infos' do
      for tag in info.metadata.tags do
         tag_formalized_counts :=
          tag_formalized_counts.set! tag.toNat ((tag_formalized_counts[tag.toNat]!) + 1)
         if info.proved then
          tag_solved_counts :=
           tag_solved_counts.set! tag.toNat ((tag_solved_counts[tag.toNat]!) + 1)
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
    h.putStrLn (←footer)
    h.putStr "</body></html>"

    -- now write index.html
    let h ← IO.FS.Handle.mk "_site/index.html" IO.FS.Mode.write
    h.putStrLn <| ←htmlHeader "Compfiles: Catalog of Math Problems Formalized in Lean"
    h.putStrLn <| ← topbar "about"
    h.putStrLn "<p>"
    h.putStrLn s!"Welcome to Compfiles, a collaborative repository of olympiad-style math problems that have been formalized in the <a class=\"external\" href=\"https://leanprover-community.github.io/\">Lean</a> theorem prover."
    h.putStrLn "</p>"
    h.putStrLn "<p>"
    h.putStrLn <| s!"So far, <a href=\"{←getBaseUrl}all.html\"><b>{infos.length}</b> problems and <b>{num_proved}</b> solutions</a> have been formalized."
    h.putStrLn "</p>"
    h.putStr "<div class=\"toplevel-tables\"><table class=\"toplevel-olympiad-stats\">"
    h.putStr "<thead><tr><th></th><th title=\"This total includes problems not added to Compfiles.\">Total</th><th>Formalized</th><th>Solved</th></tr></thead>"
    h.putStr "<tbody>"
    h.putStr s!"<tr><th><a href=\"imo.html\">IMO</a></th><td>{totalImoProblemCount}</td><td>{imoFormalizedCount}</td><td>{imoSolvedCount}</td></tr>"
    h.putStr s!"<tr><th><a href=\"usamo.html\">USAMO</a></th><td>{totalUsamoProblemCount}</td><td>{usamoFormalizedCount}</td><td>{usamoSolvedCount}</td></tr>"
    h.putStr "</tbody>"
    h.putStr "</table>"

    h.putStr "<table class=\"toplevel-tag-stats\">"
    h.putStr "<thead><tr><th></th><th>Formalized</th><th>Solved</th></tr></thead>"
    h.putStr "<tbody>"
    h.putStr "<tr><th>Algebra</th>"
    h.putStr s!"<td>{tag_formalized_counts[ProblemExtraction.ProblemTag.Algebra.toNat]!}</td>"
    h.putStr s!"<td>{tag_solved_counts[ProblemExtraction.ProblemTag.Algebra.toNat]!}</td>"
    h.putStr "</tr>"
    h.putStr "<tr><th>Number Theory</th>"
    h.putStr s!"<td>{tag_formalized_counts[ProblemExtraction.ProblemTag.NumberTheory.toNat]!}</td>"
    h.putStr s!"<td>{tag_solved_counts[ProblemExtraction.ProblemTag.NumberTheory.toNat]!}</td>"
    h.putStr "</tr>"
    h.putStr "<tr><th>Combinatorics</th>"
    h.putStr s!"<td>{tag_formalized_counts[ProblemExtraction.ProblemTag.Combinatorics.toNat]!}</td>"
    h.putStr s!"<td>{tag_solved_counts[ProblemExtraction.ProblemTag.Combinatorics.toNat]!}</td>"
    h.putStr "</tr>"
    h.putStr "<tr><th>Geometry</th>"
    h.putStr s!"<td>{tag_formalized_counts[ProblemExtraction.ProblemTag.Geometry.toNat]!}</td>"
    h.putStr s!"<td>{tag_solved_counts[ProblemExtraction.ProblemTag.Geometry.toNat]!}</td>"
    h.putStr "</tr>"
    h.putStr "</tbody>"
    h.putStr "</table></div>"

    faq h

    h.putStrLn (←footer)
    h.putStr "</body></html>"

    let h ← IO.FS.Handle.mk "_site/imo.html" IO.FS.Mode.write
    h.putStrLn <| ←htmlHeader "Compfiles: Catalog of Math Problems Formalized in Lean"
    h.putStrLn <| ← topbar "imo"
    h.putStrLn <|
      s!"<p>Since 1959, the International Mathematical Olympiad has included a total of <b>{totalImoProblemCount}</b> problems.</p>"
    let formalizedPercent := stringifyPercent <|
      (OfNat.ofNat imoFormalizedCount) / (OfNat.ofNat totalImoProblemCount)
    h.putStrLn <| s!"<p><b>{imoFormalizedCount}</b> problems have been formalized ({formalizedPercent}).</p>"
    let solvedPercent := stringifyPercent <|
      (OfNat.ofNat imoSolvedCount) / (OfNat.ofNat totalImoProblemCount)
    h.putStrLn <| s!"<p><b>{imoSolvedCount}</b> problems have complete formalized solutions ({solvedPercent}).</p>"
    h.putStr "<table class=\"full-problem-grid\">"
    for ⟨year, count⟩ in imoProblemCounts do
      h.putStr s!"<tr><td class=\"year\">{year}</td>"
      for ii in List.range count do
        let idx := ii + 1
        let name := s!"Imo{year}P{idx}"
        let path := s!"problems/Compfiles.{name}.html"
        let cls ← match infomap.find? name with
        | .some info =>
          pure (if info.proved then "proved" else "formalized")
        | .none =>
          generateProblemStubFile path name
          pure "todo"

        h.putStr s!"<td class=\"{cls}\"><a href=\"{path}\">P{idx}</a></td>"
        pure ()
      h.putStrLn "</tr>"
    h.putStr "</table>"

    h.putStrLn (←footer)
    h.putStr "</body></html>"
    pure ()

    let h ← IO.FS.Handle.mk "_site/usamo.html" IO.FS.Mode.write
    h.putStrLn <| ←htmlHeader "Compfiles: Catalog of Math Problems Formalized in Lean"
    h.putStrLn <| ← topbar "usamo"
    h.putStrLn <|
      "<p>Since 1972, the USA Mathematical Olympiad has included a total of " ++
      s!"<b>{totalUsamoProblemCount}</b> problems.</p>"
    let formalizedPercent := stringifyPercent <|
      (OfNat.ofNat usamoFormalizedCount) / (OfNat.ofNat totalUsamoProblemCount)
    h.putStrLn <|
      s!"<p><b>{usamoFormalizedCount}</b> problems have been formalized ({formalizedPercent}).</p>"
    let solvedPercent := stringifyPercent <|
      (OfNat.ofNat usamoSolvedCount) / (OfNat.ofNat totalUsamoProblemCount)
    h.putStrLn <|
      s!"<p><b>{usamoSolvedCount}</b> problems have complete formalized solutions ({solvedPercent}).</p>"
    h.putStr "<table class=\"full-problem-grid\">"
    for ⟨year, count⟩ in usamoProblemCounts do
      h.putStr s!"<tr><td class=\"year\">{year}</td>"
      for ii in List.range count do
        let idx := ii + 1
        let name := s!"Usa{year}P{idx}"
        let path := s!"problems/Compfiles.{name}.html"

        let cls ← match infomap.find? name with
        | .some info =>
           pure (if info.proved then "proved" else "formalized")
        | .none =>
           generateProblemStubFile path name
           pure "todo"

        h.putStr s!"<td class=\"{cls}\"><a href=\"{path}\">P{idx}</a></td>"
        pure ()
      h.putStrLn "</tr>"
    h.putStr "</table>"

    h.putStrLn (←footer)
    h.putStr "</body></html>"
    pure ()
