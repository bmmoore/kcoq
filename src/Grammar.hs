{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ImplicitParams #-}
{-|
Description: Types for K syntax declarations
 -}
module Grammar where
import Data.String
import Data.Data

import Data.List(intercalate,intersperse)
import Control.Applicative

import Attributes

newtype Sort = Sort {sortName :: String}
  deriving (Eq,Ord,Data,Typeable)
instance IsString Sort where
  fromString = Sort
instance Show Sort where
  show (Sort s) = s

newtype Label = Label String
  deriving (Eq,Ord,Data,Typeable)
instance IsString Label where
  fromString = Label

data Associativity = AssocLeft | AssocRight | NonAssoc
  deriving (Eq,Data,Typeable)

data NoFollow = NoFollow String [String]
  deriving (Eq,Data,Typeable)

data Syntax = Syntax Sort Attributes [ProductionGroup]
            | ListSyntax Sort Attributes ListProduction
  -- invariant: inner lists non-empty
  deriving (Eq,Data,Typeable)

instance HasAttributes Syntax where
  attributes f (Syntax s attrs groups) = (\attrs' -> Syntax s attrs' groups) <$> f attrs
  attributes f (ListSyntax s attrs prod) = (\attrs' -> ListSyntax s attrs' prod) <$> f attrs

isListSyntax :: Syntax -> Bool
isListSyntax (ListSyntax{}) = True
isListSyntax _ = False

syntaxSort :: Syntax -> Sort
syntaxSort (Syntax name _ _) = name
syntaxSort (ListSyntax name _ _) = name

data ProductionGroup = ProductionGroup (Maybe Associativity) [Production]
  deriving (Eq,Data,Typeable)
groupProductions :: ProductionGroup -> [Production]
groupProductions (ProductionGroup _ ps) = ps
data Production = Production [Either String Sort] Attributes
                | LabelProduction (Maybe Label) [Sort] Attributes
                | TokenProduction String Attributes
  deriving (Eq,Ord,Data,Typeable)
instance HasAttributes Production where
  attributes f (Production items a) = Production items <$> f a
  attributes f (LabelProduction l args a) = LabelProduction l args <$> f a
  attributes f (TokenProduction tok a) = TokenProduction tok <$> f a

isFunctionProd :: Production -> Bool
isFunctionProd t = any (\attr -> hasAttr attr t) ["function", "predicate", "hook"]

labelProductionItems :: Maybe Label -> [Sort] -> [Either String Sort]
labelProductionItems mbLabel args =
  (case mbLabel of
      Nothing -> []
      Just (Label l) -> [Left l])++
  Left "(":
  intersperse (Left ",") (map Right args)
  ++[Left ")"]

isSubsorting :: Production -> Bool
isSubsorting (Production [Right _] attrs)
  | Nothing <- getAttr "klabel" attrs = True
isSubsorting _ = False

defaultLabel :: [Either String Sort] -> Maybe Label
defaultLabel [Right _] = Nothing
defaultLabel items = Just (Label ('\'':concatMap (either id (const "_")) items))

noQuoteLabel :: [Either String Sort] -> Maybe Label
noQuoteLabel [Right _] = Nothing
noQuoteLabel items = Just (Label (concatMap (either id (const "_")) items))

type LabelScheme = (?defaultLabel :: [Either String Sort] -> Maybe Label)

-- returns the label, or Nothing if
-- this production should not produce a label
prodLabel :: (LabelScheme) => Production -> Maybe Label
prodLabel (Production _ attrs)
  | Just label <- getAttr "klabel" attrs = Just (Label label)
prodLabel (Production items attrs)
  | Just _ <- getAttr "bracket" attrs =
    if length [s :: Sort | Right s <- items] == 1
    then Nothing
    else error $ "bracket attribute only legal with exactly one nonterminal"
prodLabel (Production items _) = ?defaultLabel items
prodLabel (LabelProduction (Just _) _ attrs)
  | Just label <- getAttr "klabel" attrs = Just (Label label)
prodLabel (LabelProduction Nothing [_] attrs)
  | Just _ <- getAttr "bracket" attrs = Nothing
prodLabel (LabelProduction _ _ attrs)
  | Just _ <- getAttr "bracket" attrs
    = error "bracket attribute not legal on tuple or function productions"
prodLabel (LabelProduction (Just (Label label)) _ _) = ?defaultLabel [Left label]
prodLabel (LabelProduction Nothing args _)
  = Just (Label ('(':intersperse ',' (map (const '_') args)++")"))
prodLabel (TokenProduction _ _) = Nothing

prodArgs :: Production -> [Sort]
prodArgs (Production items _) = [s | Right s <- items]
prodArgs (LabelProduction _ args _) = args
prodArgs (TokenProduction _ _) = []

data ListProduction = ListProduction {listProdElement :: Sort
                                     ,listProdSep :: String
                                     ,listNonEmpty :: Bool
                                     ,listAttributes ::Attributes
                                     }
  deriving (Eq,Ord,Data,Typeable)
instance HasAttributes ListProduction where
  attributes f (ListProduction el sep nonEmpty attrs) =
    ListProduction el sep nonEmpty <$> f attrs

-- | takes list sort and the list production, and returns
-- the cons label to use
listProdSepLabel :: Sort -> ListProduction -> Label
listProdSepLabel listSort p =
  case getAttr "klabel" p of
    Just l -> Label l
    Nothing -> Label ("_"++listProdSep p++show listSort++"_")

data Priorities = Priorities [[Label]]
  deriving (Eq,Data,Typeable)

indentString :: Int -> String -> String
indentString n str = go str
  where pad = replicate n ' '
        go ('\n':cs) = '\n':pad++go cs
        go (c:cs) = c:go cs
        go [] = []

-- moderately pretty Show
instance Show Associativity where
  show AssocLeft = "left"
  show AssocRight = "right"
  show NonAssoc = "non-assoc"

instance Show NoFollow where
  show (NoFollow token sets) =
    "syntax "++show token++" -/- "++intercalate "." ["["++set++"]" | set <- sets]

instance Show Syntax where
  show (Syntax name attrs prodGroups) =
    let header = "syntax "++sortName name++showAttrs attrs
    in header ++ if null prodGroups then "\n" else " ::= "++
         indentString (length header + 3)
           (intercalate ("\n> ") (map show prodGroups))
  show (ListSyntax name attrs prod) =
    "syntax "++sortName name++showAttrs attrs++" ::= "++show prod
instance Show ProductionGroup where
  show (ProductionGroup mbAssoc prods) =
    (case mbAssoc of
        Nothing -> ""
        Just a -> show a++":\n  ") ++
    intercalate "\n| " (map show prods)
instance Show ListProduction where
  show (ListProduction sort separator nonEmpty attrs) =
    let opening = if nonEmpty then "NeList{" else "List{" in
    opening++sortName sort++","++show separator++"}"++showAttrs attrs
instance Show Production where
  show (Production items attrs)
    = unwords (map (either show sortName) items)++showAttrs attrs
  show (LabelProduction label args attrs)
    = maybe "" show label
      ++"("++intercalate ", " (map sortName args)++")"++showAttrs attrs
  show (TokenProduction regexp attrs) =
    "Token{"++regexp++"}"++showAttrs attrs

instance Show Label where
  show (Label l) = l
instance Show Priorities where
  show (Priorities blocks) = "syntax priorities "
    ++ intercalate " > " (map (unwords . map show) blocks)
