module Synquid.HtmlOutput (
  docHtml, 
  showDocHtml, 
  renderHtmlNoHeader
  ) where

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import System.Console.ANSI
import Text.Html

-- | Render a document into an html object.
docHtml :: PP.SimpleDoc -> Html
docHtml doc = splitLines [] 0 (PP.SSGR []) doc

-- | Render a document into a string that contains the html code.
showDocHtml :: PP.SimpleDoc -> String
showDocHtml = renderHtmlNoHeader . docHtml

renderHtmlNoHeader :: Html -> String
renderHtmlNoHeader theHtml = foldr (.) id (map (renderHtml' 0) (getHtmlElements theHtml)) "\n"

-- | Width in pixels of a single indentation position.
indentWidth = 7

-- | String that represents a CSS attribute with given key and value.
cssAttr key val = key ++ ": " ++ val ++ ";"    

-- | Apply a funtion to HTML content if it is non-empty
applyToNonEmpty f content = if isNoHtml content 
  then noHtml 
  else f content  
      
-- | 'splitLines' @sgrs indent currentLine next@ : 
-- Generate HTML for a document where the current line is indented by @indent@, starts with @currentLine@ and the current formating settings are @sgrs@,
-- while @next@ is the rest of the document.
-- We maintain that each line starts with a formatting operation.
splitLines :: [SGR] -> Int -> (PP.SimpleDoc -> PP.SimpleDoc) -> PP.SimpleDoc -> Html 
splitLines sgrs indent currentLine next = case next of
  PP.SEmpty -> genLine
  PP.SChar c doc -> splitLines sgrs indent (currentLine . PP.SChar c) doc
  PP.SText len s doc -> splitLines sgrs indent (currentLine . PP.SText len s) doc
  PP.SLine indent' doc -> genLine +++ splitLines sgrs indent' (PP.SSGR sgrs) doc
  PP.SSGR sgrs' doc -> splitLines sgrs' indent (currentLine . PP.SSGR sgrs') doc
  where
    genLine = thediv ! [thestyle (cssAttr "margin-left" $ show indentPX ++ "px")] $ line
    indentPX = indent * indentWidth
    line = if isNoHtml content then spaceHtml else content
    content = splitStyles [] id (currentLine PP.SEmpty)    
    
-- | 'splitStyles' @sgrs currentSpan next@ :
-- Generate HTML for a line where the current uni-formatted span of text starts with @currentSpan@ and has formatiing settings @sgrs@,
-- while @next@ is the rest of the line.
-- @next@ must not contain new lines.
splitStyles :: [SGR] -> (PP.SimpleDoc -> PP.SimpleDoc) -> PP.SimpleDoc -> Html
splitStyles sgrs currentSpan next = case next of
  PP.SEmpty -> genSpan sgrs currentSpan
  PP.SChar c doc -> splitStyles sgrs (currentSpan . PP.SChar c) doc
  PP.SText len s doc -> splitStyles sgrs (currentSpan . PP.SText len s) doc
  PP.SLine _ _ -> error "newline in splitStyles"
  PP.SSGR sgrs' doc -> genSpan sgrs currentSpan +++ splitStyles sgrs' id doc  
  where    
    genSpan [] currentSpan = simple (currentSpan PP.SEmpty)  
    genSpan [Reset] currentSpan = simple (currentSpan PP.SEmpty)  
    genSpan sgrs currentSpan = applyToNonEmpty 
      (thespan ! [thestyle (concatMap sgrToCss sgrs)]) 
      (simple $ currentSpan PP.SEmpty)

    sgrToCss (SetConsoleIntensity BoldIntensity)    = cssAttr "font-weight" "bold"
    sgrToCss (SetConsoleIntensity NormalIntensity)  = cssAttr "font-weight" "normal"
    sgrToCss (SetItalicized True)                   = cssAttr "font-style" "italic"
    sgrToCss (SetItalicized False)                  = cssAttr "font-style" "normal"
    sgrToCss (SetUnderlining SingleUnderline)       = cssAttr "text-decoration" "underline"
    sgrToCss (SetUnderlining NoUnderline)           = cssAttr "text-decoration" "none"
    sgrToCss (SetColor Foreground intensity color)  = cssAttr "color" $ sgrColor intensity color
    sgrToCss (SetColor Background intensity color)  = cssAttr "background-color" $ sgrColor intensity color
    sgrToCss _ = ""

    sgrColor _ Black        = "Black"
    sgrColor Vivid Red      = "Red"
    sgrColor Vivid Green    = "Green"
    sgrColor Vivid Yellow   = "Yellow"
    sgrColor Vivid Blue     = "Blue"
    sgrColor Vivid Magenta  = "Magenta"
    sgrColor Vivid Cyan     = "Cyan"
    sgrColor Vivid White    = "While"
    sgrColor Dull Red       = "DarkRed"
    sgrColor Dull Green     = "DarkGreen"
    sgrColor Dull Yellow    = "DarkKhaki"
    sgrColor Dull Blue      = "DarkBlue"
    sgrColor Dull Magenta   = "DarkMagenta"
    sgrColor Dull Cyan      = "DarkCyan"
    sgrColor Dull White     = "Gray"    

-- | Generate HTML for documents that do not contain new lines or formatting.
simple PP.SEmpty  = noHtml
simple (PP.SChar c doc) = toHtml c +++ simple doc
simple (PP.SText _ s doc) = toHtml s +++ simple doc   
simple (PP.SLine indent doc) = error "newline in simple"
simple (PP.SSGR sgrs doc) = error "formatting in simple"    
      