import Dashboard.Common
import SSG.Html
import SSG.Tags

def compAnchor (config : SConfig) (text : String) (rel : List String) : Html :=
  .a (config.resolveRel rel) [] text
