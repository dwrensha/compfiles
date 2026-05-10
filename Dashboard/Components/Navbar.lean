import Dashboard.Common
import SSG.Html

open Html

inductive NavbarState where
| about
| imo
| usamo
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
    renderTab "About" (config.resolveRel ["index.html"]) (currentPage == .about),
    renderTab "IMO" (config.resolveRel ["imo.html"]) (currentPage == .imo),
    renderTab "USAMO" (config.resolveRel ["usamo.html"]) (currentPage == .usamo),
    renderTab "All" (config.resolveRel ["all.html"]) (currentPage == .all),
  ]
]
