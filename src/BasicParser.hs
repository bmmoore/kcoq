{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE NamedFieldPuns           #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
{-|
Description: Parser for basic syntax of definition
 -}
module BasicParser where
import           Data.Char
import           Data.Data
import           OpenTokenParser
import           Text.Parsec                hiding (label, (<|>))
import           Text.Parsec.Error
import           Text.Parsec.Language       (emptyDef)
import           Text.Parsec.Pos            (newPos)
import           Text.Parsec.String         (Parser, parseFromFile)
import qualified Text.Parsec.Token          as T

import           Language.Haskell.TH.Quote
import           Language.Haskell.TH.Syntax (Loc (..), qLocation)

import           Control.Applicative        hiding (many, optional)

import           Attributes
import           Definition
import           Grammar
import           Module hiding (moduleName)

optionMb :: Parser a -> Parser (Maybe a)
optionMb p = option Nothing (Just <$> p)

-- Language basics:

-- keywords that introduce a block, split into those that might
-- otherwise be an identifier, and the doc comment openings
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
parens, brackets, lexeme :: Parser a -> Parser a
parens = T.parens lexer
brackets = T.brackets lexer
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

hashed :: Parser String -> Parser String
hashed name = (:) <$> char '#' <*> name <|> name

-- A '-' is legal in module names, but not other identifiers
moduleName :: Parser ModuleName
moduleName = lexeme $ ModuleName <$>
   hashed ((:) <$> satisfy isAlpha <*> many (satisfy (\c -> isAlphaNum c || c == '-')))


-- Parsing
-- TODO: first case rejects e.g. #syntax, but that isn't necessarily reserved..
-- but maybe it needs to be to end rules?
hashIdentifier :: Parser String
hashIdentifier = hashed identifier

label :: Parser Label
label = lexeme (Label <$> liftA2 (:) (char '\'') (many1 (satisfy (not . isSpace))))
    <|> Label <$> hashIdentifier
    <?> "label"

sort :: Parser Sort
sort = Sort <$> hashIdentifier <?> "sort"

{-
  Attribute syntax should be
  ("[" TagListDz "]")?, TagListDz being a comma separated list of
  Key# | Key#(TagContent#) | Key#(##String),
  where
  Key#  [a-z][A-Za-z0-9-]*
  TagContent# is any but [\n\r"], where parens balance
 -}

attr :: Parser Attribute
attr = Attribute <$> attrName <*> option "" (parens attrContents)
 <?> "attribute"
 where attrName = lexeme (many1 (satisfy (\c -> isAlpha c || c == '-')))
       attrContents = concat <$> many attrContent
       attrContent =
             many1 (satisfy (\c -> c /= '(' && c /= ')' && c /= '\n'))
         <|> (\s -> '(':s++")") <$ char '(' <*> attrContents <* char ')'

optAttrs :: Parser [Attribute]
optAttrs = option [] (brackets (commaSep attr) <?> "attributes")

listProduction :: Parser ListProduction
listProduction = do
  nonEmpty <- True <$ reserved "NeList" <|> False <$ reserved "List"
  ListProduction <$  symbol "{"
                 <*> sort
                 <*  comma
                 <*> stringLiteral
                 <*> pure nonEmpty
                 <*  symbol "}"
                 <*> optAttrs

production :: Parser Production
production = (try $ LabelProduction <$> optionMb label
                                    <*> parens (commaSep sort)
                                    <*> optAttrs)

         <|> (try $ TokenProduction <$ reserved "Token"
                                    <*  char '{'
                                    <*> many (satisfy (\c -> c /='}' && c /= '\\')
                                              <|> (char '\\' >> anyChar))
                                    <*  symbol "}"
                                    <*> optAttrs)
         <|> Production <$> many1 (    Left <$> stringLiteral
                                  <|> Right <$> sort
                                  <?> "production item")
                        <*> optAttrs
         <|> Production [] <$ symbol "." -- empty production
                           <*> optAttrs
      <?> "production"

productionGroup :: Parser ProductionGroup
productionGroup = ProductionGroup
  <$> option Nothing
      (try (Just <$> ( AssocLeft <$ symbol "left:"
                 <|> AssocRight <$ symbol "right:"
                 <|> NonAssoc <$ symbol "non-assoc:")))
  <*> sepBy1 production (reservedOp "|")

syntax :: Parser Syntax
syntax = do reserved "syntax"
            name <- sort
            attrs <- optAttrs
            reservedOp "::=" *>
             (try (ListSyntax name attrs <$> listProduction)
                <|> Syntax name attrs <$> sepBy1 productionGroup (reservedOp ">"))
             <|> pure (Syntax name attrs [])

  <?> "syntax declaration"

imports :: Parser ModuleName
imports = reserved "imports" *> moduleName

-- TODO: analyze the end a bit more, and not capture following doc comments
bubble :: Parser String
bubble = normBody . concat <$> lexeme (manyTill bubbleBit (lookAhead stopWord))
  where stopWord = foldr (<|>) eof [try (() <$ reserved s) | s <- bubbleEnd]
        normBody str = reverse . dropWhile isSpace . reverse $ str
        -- use this rather than just anyChar so we don't
        -- break if the bubble is followed by an ordinary comment
        -- containing the characters "rule"
        bubbleBit = (:[]) <$> satisfy (\c -> c /= '/' && c /= '"')
              <|> lineComment
              <|> multiLineComment
              <|> bubbleString
              <|> string "/"
        bubbleString = (\chars -> '"':concat chars++"\"") <$>
            between (char '"') (char '"')
            (many ((:[]) <$> satisfy (\c -> c /= '\\' && c /= '"')
                   <|> ((\c1 c2 -> c1:[c2]) <$> char '\\' <*> anyChar)))


rule :: Parser String
rule = reserved "rule" *> bubble

context :: Parser String
context = reserved "context" *> bubble

configuration :: Parser String
configuration = reserved "configuration" *> bubble

priorities :: Parser Priorities
priorities = Priorities
  <$  reserved "syntax"
  <*  reserved "priorities"
  <*> sepBy (many1 label) (symbol ">")

noFollow :: Parser NoFollow
noFollow = NoFollow
  <$  reserved "syntax"
  <*> stringLiteral
  <*  symbol "-/-"
  <*> lexeme (sepBy1 (between (char '[') (char ']') (many1 (satisfy (/=']')))) (char '.'))

moduleItem :: Parser ModuleItem
moduleItem = PriorityItem <$> try priorities
         <|> NoFollowItem <$> try noFollow
         <|> SyntaxItem <$> syntax
         <|> ImportsItem <$> imports
         <|> ModuleCommentItem <$> comment
         <|> RuleItem <$> rule
         <|> ContextItem <$> context
         <|> ConfigurationItem <$> configuration

kmodule :: Parser Module
kmodule = Module <$  reserved "module"
                 <*> moduleName
                 <*> many moduleItem
                 <* reserved "endmodule"
            <?> "module"

requireItem :: Parser String
requireItem = reserved "require" *> stringLiteral <?> "require"

kdefinition :: Parser Definition
kdefinition = do
  leading <- many (RequireItem <$> requireItem
               <|> DefinitionCommentItem <$> comment)
  following <- many (DefinitionCommentItem <$> comment           
                 <|> ModuleItem <$> kmodule)
  return (Definition (leading++following))

-- parse a definition, returning the requires early.
-- The outer Either returns a parse error while getting
-- the prefix of requires,
-- the inner Either has parse errors from the rest of the definition
-- the Definition has all items from the file, including the Requires
splitParse :: SourceName -> String -> Either ParseError ([String],Either ParseError Definition)
splitParse inputName input = do
  let getStart = do
        whiteSpace
        leading <- many (RequireItem <$> requireItem
                         <|> DefinitionCommentItem <$> comment)
        state <- getParserState
        return (leading,state)
      getRest leading state = do
        setParserState state
        following <- many (DefinitionCommentItem <$> comment
           <|> ModuleItem <$> kmodule)
        eof
        return (Definition (leading++following))
  (leading,state) <- parse getStart inputName input
  let requires = [req | RequireItem req <- leading]
  return (requires, parse (getRest leading state) inputName "")

basicParseFile :: FilePath -> IO (Either ParseError Definition)
basicParseFile = parseFromFile (whiteSpace *> kdefinition <* eof)

splitParseFile :: FilePath -> IO (Either ParseError ([String],Either ParseError Definition))
splitParseFile fname = do input <- readFile fname
                          return (splitParse fname input)

-- quasi-quoters
parsecQuasiExp :: (Data a) => Parser a -> QuasiQuoter
parsecQuasiExp p = QuasiQuoter (\str -> do
  loc <- qLocation
  let parsecLoc = uncurry (newPos (loc_filename loc)) (loc_start loc)
      fmtMessages = showErrorMessages "or" "Unknown parse error" "Expecting" "Unexpected" "EOF"
      fmtPos epos = sourceName epos++":"++show (sourceLine epos)++":"++show (sourceColumn epos)++":"
  case parse (setPosition parsecLoc >> p) (loc_filename loc) str of
    Left err -> fail $
      let epos = errorPos err
          msgs = errorMessages err
      in fmtPos epos++fmtMessages msgs
    Right result -> dataToExpQ (const Nothing) result
  )
  (error "pattern quotes not supported")
  (error "type quotes not supported")
  (error "declaration quotes not supported")

mkQQ :: (Data a) => Parser a -> QuasiQuoter
mkQQ parser = parsecQuasiExp (whiteSpace *> parser <* eof)

ksyn :: QuasiQuoter
ksyn = mkQQ syntax

ksyns :: QuasiQuoter
ksyns = mkQQ (many1 syntax)

kdef :: QuasiQuoter
kdef = mkQQ kdefinition

prod :: QuasiQuoter
prod = mkQQ production
