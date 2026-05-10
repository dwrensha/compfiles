module

public import SSG.Util

@[expose] public section

/-- A single HTML attribute -/
abbrev Attr := String × String

/-- HTML document tree. Structural correctness by construction. -/
inductive Html where
/-- Raw HTML string, NOT escaped. Use with caution. -/
| raw (s : String)
/-- Text content, auto-escaped. -/
| text (s : String)
/-- Normal element: <tag attrs>children</tag> -/
| elem (tag : String) (attrs : List Attr) (children : List Html)
/-- Void element (self-closing): <br>, <img>, <hr>, <meta>, <link>, etc. -/
| void (tag : String) (attrs : List Attr)
/-- Fragment: multiple nodes without a wrapper -/
| fragment (nodes : List Html)
deriving Inhabited

namespace Html

/-- Render to string -/
partial def render : Html → String
| .raw s => s
| .text s => htmlEscape s
| .void tag attrs => s!"<{tag}{renderAttrs attrs}>"
| .elem tag attrs children =>
  let inner := String.join (children.map render)
  s!"<{tag}{renderAttrs attrs}>{inner}</{tag}>"
| .fragment nodes => String.join (nodes.map render)
where
  renderAttrs (attrs : List Attr) : String :=
    attrs.foldl (fun acc (k, v) => acc ++ s!" {k}=\"{htmlEscapeAttr v}\"") ""

/-- Render a full HTML5 document with doctype -/
def renderDoc (h : Html) : String :=
  s!"<!DOCTYPE html>\n{h.render}"

instance : Coe String Html where
  coe s := text s

instance : Coe Html (List Html) where
  coe h := [h]

instance : Coe String (List Html) where
  coe s := [text s]

end Html

end
