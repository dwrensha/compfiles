import SSG.Core
import SSG.Html
import SSG.Tags

import Dashboard.Assets

structure Config where
  commitHash : String

instance : ToString Config where
  toString := fun c ↦ s!"@{c.commitHash}"

abbrev SConfig := SiteConfig Config
