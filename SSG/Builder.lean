module

public import SSG.Core

/-! Site building engine -/

@[expose] public section

open System (FilePath)

/-- Copy a single asset -/
def copyAsset (outDir : String) : Asset → IO Unit
  | .file src dst => do
    let content ← IO.FS.readFile src
    IO.FS.writeFile (outDir ++ "/" ++ dst) content
  | .binary src dst => do
    let content ← IO.FS.readBinFile src
    IO.FS.writeBinFile (outDir ++ "/" ++ dst) content

/-- Write a single page -/
def writePage (outDir : String) (page : Page) : IO Unit := do
  let fullPath := outDir ++ "/" ++ page.path
  if let some dir := FilePath.parent fullPath then
    IO.FS.createDirAll dir.toString
  let content ← page.content
  IO.FS.writeFile fullPath content
  IO.println s!"Generated {page.path}"

/-- Build the entire site -/
def buildSite {Custom : Type} [ToString Custom] (config : SiteConfig Custom)
  (assets : List Asset) (pages : List Page) : IO Unit := do
  IO.println s!"Building Config:\n{config}"
  IO.println s!"Building site to {config.outDir}..."
  IO.FS.createDirAll config.outDir
  -- Copy assets
  for asset in assets do
    copyAsset config.outDir asset
  -- Generate pages
  for page in pages do
    writePage config.outDir page

  IO.println s!"✓ Built {pages.length} pages"
