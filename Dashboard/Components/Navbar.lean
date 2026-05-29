import Dashboard.Common
import SSG.Html

open Html

inductive NavbarState where
| about
| imo
| usamo
| misc
| all
| none
deriving BEq

def renderTab (txt : String) (href : String) (pred : Bool) : Html :=
  if pred then .span [cls "active"] txt
  else .span [cls "inactive"] [.a (href) [] txt]

def navbar (config : SConfig) (currentPage : NavbarState) : List Html := [
  .h2 [] [
    .a "https://github.com/dwrensha/compfiles" [cls "external"] "Compfiles",
    ": Catalog Of Math Problems Formalized In Lean",
  ],
  .div [cls "navbar"] [
    renderTab "About" (config.resolveAbs ["index.html"]) (currentPage == .about),
    renderTab "IMO" (config.resolveAbs ["imo.html"]) (currentPage == .imo),
    renderTab "USAMO" (config.resolveAbs ["usamo.html"]) (currentPage == .usamo),
    renderTab "Misc" (config.resolveAbs ["misc.html"]) (currentPage == .misc),
    renderTab "All" (config.resolveAbs ["all.html"]) (currentPage == .all),
  ]
]
