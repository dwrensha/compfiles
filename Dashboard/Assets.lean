module

public import SSG.Core

@[expose] public section

namespace Assets

def mainCss : Asset := Asset.file "assets/main.css" "/main.css"
def doccoCss : Asset := Asset.file "assets/docco.css" "/docco.css"
def highlightMinJs : Asset :=
  Asset.file "assets/highlight.min.js" "/highlight.min.js"
def leanJs : Asset := Asset.file "assets/lean.js" "/lean.js"
def faviconIco : Asset := Asset.binary "assets/favicon.ico" "/favicon.ico"
def appleTouchIconPng : Asset :=
  Asset.binary "assets/apple-touch-icon.png" "/apple-touch-icon.png"
def ogPreviewPng : Asset :=
  Asset.binary "assets/og-preview.png" "/og-preview.png"

end Assets

end
