module

public import SSG.Html

@[expose] public section

open Html

namespace Html

def head (c : List Html) := elem "head" [] c
def html (attrs : List Attr := []) (c : List Html) := elem "html" attrs c
def body (attrs : List Attr := []) (c : List Html) := elem "body" attrs c
def script (attrs : List Attr) (c : List Html) := elem "script" attrs c

def div (attrs : List Attr := []) (c : List Html) := elem "div" attrs c
def span (attrs : List Attr := []) (c : List Html) := elem "span" attrs c
def nav (attrs : List Attr := []) (c : List Html) := elem "nav" attrs c
def main_ (attrs : List Attr := []) (c : List Html) := elem "main" attrs c
def header (attrs : List Attr := []) (c : List Html) := elem "header" attrs c
def footer (attrs : List Attr := []) (c : List Html) := elem "footer" attrs c
def section_ (attrs : List Attr := []) (c : List Html) := elem "section" attrs c

def title (attrs : List Attr := []) (c : List Html) := elem "title" attrs c
def h1 (attrs : List Attr := []) (c : List Html) := elem "h1" attrs c
def h2 (attrs : List Attr := []) (c : List Html) := elem "h2" attrs c
def h3 (attrs : List Attr := []) (c : List Html) := elem "h3" attrs c
def h4 (attrs : List Attr := []) (c : List Html) := elem "h4" attrs c
def p (attrs : List Attr := []) (c : List Html) := elem "p" attrs c
def a (href : String) (attrs : List Attr := []) (c : List Html) :=
  elem "a" (("href", href) :: attrs) c
def b (attrs : List Attr := []) (c : List Html) := elem "b" attrs c
def ul (attrs : List Attr := []) (c : List Html) := elem "ul" attrs c
def li (attrs : List Attr := []) (c : List Html) := elem "li" attrs c
def code (attrs : List Attr := []) (c : List Html) := elem "code" attrs c
def pre (attrs : List Attr := []) (c : List Html) := elem "pre" attrs c
def table (attrs : List Attr := []) (c : List Html) := elem "table" attrs c
def tbody (attrs : List Attr := []) (c : List Html) := elem "tbody" attrs c
def thead (attrs : List Attr := []) (c : List Html) := elem "thead" attrs c
def td (attrs : List Attr := []) (c : List Html) := elem "td" attrs c
def th (attrs : List Attr := []) (c : List Html) := elem "th" attrs c
def tr (attrs : List Attr := []) (c : List Html) := elem "tr" attrs c

def img (src : String) (alt : String) (attrs : List Attr := []) :=
  void "img" (("src", src) :: ("alt", alt) :: attrs)
def br := void "br" []
def hr := void "hr" []
def meta_ (attrs : List Attr) := void "meta" attrs
def link (attrs : List Attr) := void "link" attrs

def cls (c : String) : Attr := ("class", c)
def id_ (i : String) : Attr := ("id", i)

end Html

end
