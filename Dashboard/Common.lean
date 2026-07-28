module

public import SSG.Core
public import SSG.Html
public import SSG.Tags

public import Dashboard.Assets

@[expose] public section

structure Config where
  commitHash : String

instance : ToString Config where
  toString := fun c ↦ s!"@{c.commitHash}"

abbrev SConfig := SiteConfig Config
