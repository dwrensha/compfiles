import Dashboard.Common
import Dashboard.Components.Footer
import Dashboard.Components.Navbar
import SSG.Html
import SSG.Tags

open Html

def base (title : String) (config : SConfig) (currentPage : NavbarState)
  (includeHljs : Bool := false) (inner : List Html)
  : Html := html [] <| [
  .head <| [
    .meta_ [("charset", "UTF-8")],
    .meta_ [("name", "viewport"), ("content", "width=device-width")],
    .link [("href", config.resolveAsset Assets.mainCss),
      ("rel", "stylesheet"), ("type", "text/css")],
    .link [("href", config.resolveAsset Assets.faviconIco),
      ("rel", "icon"), ("type", "image/ico")],
    .link [("href", config.resolveAsset Assets.appleTouchIconPng),
      ("rel", "apple-touch-icon")],
    .meta_ [("property", "og:image"),
      ("content", config.resolveAsset Assets.ogPreviewPng)],
    .title [] [.text title],
  ] ++ if includeHljs then [
    .link [("href", config.resolveAsset Assets.doccoCss),
      ("rel", "stylesheet"), ("type", "text/css")],
    .script [("src", config.resolveAsset Assets.highlightMinJs)] [],
    .script [("src", config.resolveAsset Assets.leanJs)] [],
    .script [] "hljs.highlightAll();"
  ] else [],
  .body [] <| navbar config currentPage ++ inner ++ footerComp config
]
