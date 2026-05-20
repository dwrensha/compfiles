import Lean.Environment
import Mathlib.Data.String.Defs

import SSG.Core
import SSG.Builder

import Dashboard.Gen
import Dashboard.Assets

import ProblemExtraction

set_option linter.style.longLine false

def assets : List Asset := [
  Assets.appleTouchIconPng,
  Assets.doccoCss,
  Assets.faviconIco,
  Assets.highlightMinJs,
  Assets.leanJs,
  Assets.mainCss,
  Assets.ogPreviewPng,
]

def stripTrailingSlash (s : String) : String :=
  let chars := s.toList.reverse.dropWhile (· = '/')
  String.ofList chars.reverse

def getBaseUrl : IO String := do
  let cwd ← IO.currentDir
  let raw := (← IO.getEnv "GITHUB_PAGES_BASEURL").getD s!"file://{cwd}/_site"
  pure <| stripTrailingSlash raw

unsafe def main (_args : List String) : IO Unit := do
  let config : SConfig := {
    baseUrl := ← getBaseUrl
    outDir := "_site"
    pathPrefix := []
    custom := {
      commitHash := ((← IO.getEnv "GITHUB_SHA").getD "GITHUB_SHA_env_var_not_found")
    }
  }

  Lean.initSearchPath (← Lean.findSysroot)
  buildSite config assets (← generateAll config)
