module

public import Dashboard.Common
public import SSG.Html
public import SSG.Tags

@[expose] public section

def compAnchor (config : SConfig) (text : String) (rel : List String) : Html :=
  .a (config.resolveAbs rel) [] text
