module

@[expose] public section

/-- Escape for HTML text content -/
def htmlEscape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '&'  => "&amp;"
    | '<'  => "&lt;"
    | '>'  => "&gt;"
    | '"'  => "&quot;"
    | '\'' => "&#x27;"
    | _    => c.toString) ""

/-- Escape for HTML attribute values (superset of text escaping) -/
def htmlEscapeAttr (s : String) : String :=
  htmlEscape s

/-- Percent-encode a URI component (RFC 3986 unreserved chars preserved) -/
def uriEncodeComponent (s : String) : String :=
  s.foldl (fun acc c =>
    if c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~'
    then acc.push c
    else String.ofList [c] |>.toUTF8.foldl (fun a b =>
      s!"{a}%{hexDigit (b / 16)}{hexDigit (b % 16)}") acc) ""
where
  hexDigit (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (55 + n.toNat)

/-- Encode a full URI path (preserves / and other structure chars) -/
def uriEncodePath (s : String) : String :=
  "/".intercalate (s.splitOn "/" |>.map uriEncodeComponent)
