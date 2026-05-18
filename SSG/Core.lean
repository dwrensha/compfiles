module

/-! Core types and abstractions for the SSG -/

@[expose] public section

/-- A page to be generated -/
structure Page where
  /-- Output path relative to site root, e.g. "problems/Imo2024P1.html" -/
  path : String
  /-- Lazy content generation -/
  content : IO String
  deriving Inhabited

namespace Page

/-- Helper: create a page from static content -/
def static (path : String) (content : String) : Page :=
  { path, content := pure content }

/-- Helper: create a page from IO action -/
def dynamic (path : String) (gen : IO String) : Page :=
  { path, content := gen }

end Page

/-- A static asset to be copied -/
inductive Asset where
  | file (src dst : String)
  | binary (src dst : String)
  deriving Inhabited

namespace Asset

def src (asset : Asset) : String := match asset with
| file src _ => src
| binary src _ => src

def dst (asset : Asset) : String := match asset with
| file _ dst => dst
| binary _ dst => dst

end Asset

/-- Site-wide configuration -/
structure SiteConfig (Custom : Type) [ToString Custom] where
  outDir : String
  /-- as components WITHOUT slash -/
  pathPrefix : List String
  /-- **WITHOUT** the trailing slash -/
  baseUrl : String

  custom : Custom
deriving Inhabited

namespace SiteConfig


variable {Custom : Type} [ToString Custom]

instance : ToString (SiteConfig Custom) where
  toString := fun c ↦ "{"
    ++ s!"  outDir := {c.outDir}\n"
    ++ s!"  pathPrefix := {c.pathPrefix}\n"
    ++ s!"  baseUrl := {c.baseUrl}\n"
    ++ s!"  custom := {c.custom}\n"
    ++ "}"

def resolveRel (config : SiteConfig Custom) (path : List String) : String :=
  let parts := config.pathPrefix ++ path
  "/" ++ ("/".intercalate <| parts.filter fun p ↦ ¬ p.isEmpty)

def resolveAbs (config : SiteConfig Custom) (path : List String) : String :=
  config.baseUrl ++ "/" ++ config.resolveRel path

def resolveAsset (config : SiteConfig Custom) (asset : Asset) : String :=
  config.resolveRel <| asset.dst.split "/" |>.filterMap
    (fun s ↦ if ¬ s.isEmpty then s.toString else .none) |>.toList

end SiteConfig

/-- Page generator: takes data and produces pages -/
abbrev PageGenerator α := α → IO (List Page)
