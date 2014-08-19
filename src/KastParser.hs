{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module KastParser where
import           Data.Char
import           OpenTokenParser
import           Text.Parsec                hiding (label, (<|>))
import           Text.Parsec.Language       (emptyDef)
import           Text.Parsec.String
import qualified Text.Parsec.Token          as T

import           Control.Monad(guard)
import           Control.Applicative        hiding (many, optional)

import           BasicParser(optAttrs)
import           Attributes
import           Grammar (Label(Label),Sort(Sort))
import           Terms

type KAST = Kast () Var

reservedNames, bubbleEnd :: [String]
reservedNames = ["syntax","rule","context","configuration","endmodule"]
bubbleEnd = reservedNames++["//@","//!","/*@","/*!"]

whiteSpace :: Parser ()
whiteSpace = skipMany (simpleSpace <|> oneLineCommentGet <|> multiLineCommentGet <?> "")
  where
    simpleSpace =
        skipMany1 (satisfy isSpace)
    isDocFlag '@' = True
    isDocFlag '!' = True
    isDocFlag _ = False
    oneLineCommentGet =
        do{ try (string "//" <* notFollowedBy (satisfy isDocFlag))
          ; skipMany (satisfy (/= '\n'))
          ; return ()
          }
    multiLineCommentGet =
        do { try (string "/*" <* notFollowedBy (satisfy isDocFlag))
           ; inComment
           }
    inComment
        =   do{ try (string "*/"); return () }
        <|> do{ skipMany1 (noneOf startEnd)         ; inComment }
        <|> do{ oneOf startEnd                      ; inComment }
        <?> "end of comment"
        where
          startEnd   = "/*"

identifier, stringLiteral, comma :: Parser String
reserved, reservedOp :: String -> Parser ()
symbol :: String -> Parser String
lexer :: T.TokenParser ()
lexer@T.TokenParser
  {identifier
  ,stringLiteral
  ,reserved
  ,reservedOp
  ,comma
  ,symbol
  } = openTokenParser
        (emptyDef
         { T.reservedNames = reservedNames
         })
        (lexer {T.whiteSpace = whiteSpace})
parens, brackets, braces, lexeme :: Parser a -> Parser a
parens = T.parens lexer
brackets = T.brackets lexer
braces = T.braces lexer
lexeme = T.lexeme lexer
commaSep :: Parser a -> Parser [a]
commaSep = T.commaSep lexer

-- raw comment recognizers (used as such in parsing bubbles)
lineComment :: Parser String
lineComment = try $ (\a b c -> a ++ b ++ c)
  <$> string "//"
  <*> many (satisfy (/='\n'))
  <*> option "" (string "\n")

multiLineComment :: Parser String
multiLineComment = try $ (\a b c -> a ++ b ++ c)
  <$> string "/*"
  <*> many (satisfy (/='*') <|> try (char '*' <* notFollowedBy (char '/')))
  <*> string "*/"

-- lexeme parser for comments
comment :: Parser String
comment = lexeme (lineComment <|> multiLineComment)

variable :: Parser Var
variable = lexeme $ (Named <$> do
                      name <- (:) <$> satisfy varStart <*> many (satisfy isAlphaNum)
                      guard (name /= "HOLE")
                      return name)
                <|> Wild <$ symbol "_"
  where varStart c = isUpper c || c == '$'

backtickStr :: Parser String
backtickStr = lexeme $ do
  char '`'
  body <- many (satisfy (/='`'))
  char '`'
  return body

label :: Parser KastLabel
label = LCon . Label <$> backtickStr

ksort :: Parser Sort
ksort = lexeme $ Sort <$> ((:) <$> satisfy isUpper <*> many (satisfy isAlphaNum))

ktoken :: Parser KAST
ktoken = KWrappedLabel <$ try (symbol "#label") <*> braces (Label <$> stringLiteral)
     <|> symbol "#token" *>
         braces (Token <$> (Sort <$> stringLiteral)
                       <* comma
                       <*> stringLiteral)
{- don't need for rules
  KToken <$> backtickStr
  
 -}

kitem :: Parser KAST
kitem = foldl Annot <$> katom <*> many (symbol ":" *> ksort)
 where katom :: Parser KAST
       katom = Hole () <$ reserved "HOLE"
           <|> Var () <$> variable
           <|> try (KApp () <$> label <*> parens (option (KList []) klist))
           <|> try (Freezer () <$ reserved "#freezer" <*> parens kitem)
           <|> ktoken

klist :: Parser KAST
klist = KList[] <$ symbol ".KList"
    <|> KList <$> sepBy1 k (symbol ",")
    <?> "KList"

-- Parse a list, with some fanciness about single items
mkList :: ([a] -> a) -> Parser a -> String -> String -> Parser a
mkList con el sep nil =
      (con [] <$ symbol nil)
  <|> do e1 <- el
         trailing <- many (symbol sep >> el)
         return (case trailing of
           [] -> e1
           ts -> con (e1:ts))


kcells :: Parser KAST
kcells = Cells <$> ([] <$ symbol ".Cells" <|> many1 kcell)

endTag :: String -> Parser ()
endTag name = (try $ do
  string "</"
  symbol name
  symbol ">"
  return ())
 <?> ("end tag </"++name++">")
  
kcell :: Parser KAST
kcell = do
  name <- try (char '<' >> identifier)
  lexeme (char '>')
  ldots <- option False (try (True <$ symbol "..."))
  body <- k
  rdots <- option False (try (True <$ symbol "..."))
  endTag name
  return (Cell name ldots rdots body)

kroot :: Parser KAST
kroot  =  mkList KSequence kitem "~>" ".K"
 <|> kcells
 <?> "K"

k :: Parser KAST
k = do
  k1 <- kroot
  option k1 (KRewrite k1 <$ symbol "=>" <*> kroot)
 <?> "K term"

kastSentence :: Parser (KAST, Maybe KAST, [Attribute])
kastSentence =
  (,,) <$> k <*> option Nothing (Just <$ symbol "when" <*> k)
             <*> optAttrs
