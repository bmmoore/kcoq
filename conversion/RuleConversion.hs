{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module RuleConversion where
import           Control.Applicative
import           Control.Exception
import           Data.List (intercalate,(\\),isPrefixOf,nub,foldl')
import           Data.Char (isAlpha)
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (maybeToList,listToMaybe,fromMaybe)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.Monoid
import           Control.Monad.State
import           Control.Monad.Reader

import           Data.Foldable (foldMap,all)
import           Data.Traversable (traverse,sequenceA)
import           Prelude hiding(all)

import           Data.Data
import           Data.Data.Lens
import           GHC.Generics (Generic)
import           Control.Lens

import           Definition
import           Module
import           Grammar
import           Attributes

import           Text.Parsec (parse,eof)
import           KastParser
import           Terms

import           CoqConversion
import           TypeAnalysis

guardMb :: (Monad m) => String -> Maybe a -> m a
guardMb msg m = maybe (fail msg) return m

infoHelper :: (MonadReader s m) => Getting (First b) s b -> String -> m b
infoHelper lens msg = preview lens >>= guardMb msg

data RuleConversionInfo = RuleConversionInfo
  {_ruleCellSorts :: Map CellLabel Sort
  ,_ruleCellCons :: Map CellLabel Constructor
  ,_ruleBasicInfo :: ConversionInfo
  }
makeClassy ''RuleConversionInfo
instance HasConversionInfo RuleConversionInfo where
  conversionInfo = ruleBasicInfo

type ConversionMonad i m = (Monad m, Applicative m,
                            HasRuleConversionInfo i,
                            HasConversionInfo i,
                            MonadReader i m,
                            NamingScheme)

maximalBy :: (Ord a) => (a -> a -> Bool) -> Set a -> Set a
maximalBy isProperSubsort sorts =
  Set.filter (\s -> all (\s' -> not (isProperSubsort s s')) sorts) sorts

getGLB :: (ConversionMonad i m) => m (Set Sort -> Set Sort)
getGLB = do
  subsorts <- view convInjectionTable
  let isSubsort k1 k2 = Map.member (k1,k2) subsorts
      isProperSubsort k1 k2 = k1 /= k2 && isSubsort k1 k2
      allSorts = Set.fromList (map fst (Map.keys subsorts))
  return $ \sorts ->
    let allowed = Set.filter (\s -> all (isSubsort s) (Set.toList sorts)) allSorts
    in maximalBy isProperSubsort allowed

cellSort :: (ConversionMonad i m) => CellLabel -> m Sort
cellSort c = infoHelper (ruleCellSorts . ix c)
  ("No cell information found for cell "++show c)
cellCon :: (ConversionMonad i m) => CellLabel -> m Constructor
cellCon c = infoHelper (ruleCellCons . ix c)
  ("No cell information found for cell "++show c)

getLabelSorts :: (ConversionMonad i m) => m (Map Label (Sort,[Sort]))
getLabelSorts = view convLabelSorts
getCellSorts :: (ConversionMonad i m) => m (Map CellLabel Sort)
getCellSorts = view ruleCellSorts

getConvInfo :: (ConversionMonad i m) => m ConvInfo
getConvInfo = do
  labelCons <- view convLabelConstructors
  labelSorts <- getLabelSorts
  holes <- view convSortHoles
  injections <- view convInjectionTable
  hooks <- view convSortHooks
  boolSort <- case Map.lookup "Bool" hooks of
        Just s -> case Set.toList s of
          [boolSort] -> return boolSort
          sorts -> fail $ "Multiple sorts hooked as builtin booleans: "++unwords (map show sorts)
        Nothing -> return "#Bool"
  let trueTerm = BoolToken boolSort True
  return $ ConvInfo
    (Map.intersectionWith (\con (_,args) -> (con,args)) labelCons labelSorts)
    holes
    conForFreezer
    injections
    trueTerm

parseRule :: String -> (KAST, Maybe KAST, Attributes)
parseRule s = case parse (kastSentence <* eof) "<rule>" s of
  Left err -> error $ show err++"\nwhile parsing rule\n"++s
  Right v -> v

type NameMonad m = (Monad m, Applicative m, MonadState Int m)
nextVar :: NameMonad m => m VarId
nextVar = GenVar <$> (id <+= 1)

numberWild :: (NameMonad m) => Kast info Var -> m (Kast info VarId)
numberWild t = traverse numberVar t
  where numberVar (Named n) = pure (UserVar n)
        numberVar Wild = nextVar

renameVars :: Traversal t t' VarId String -> t -> t'
renameVars trav t =
    let userVars :: [String]
        userVars = foldMapOf (coerced trav) getVar t
        freshVars :: [String]
        freshVars = [prefix++show (i::Int) | i <- [0..]] \\ userVars
    in evalState (traverseOf trav renameVar t) freshVars
  where prefix = "WildVar"
        getVar (UserVar v) | prefix `isPrefixOf` v = [v]
        getVar _ = []
        renameVar (UserVar v) = return v
        renameVar (GenVar i) = do fresh <- get
                                  return (fresh !! i)

-- requires the top level to be a pure cell structure, with no completion needed.
-- uses supplied function on cell bodies.
gatherCells :: (Monad m, Applicative m)
            => (String -> Bool -> Bool -> Term -> m a) -> Term -> m [a]
gatherCells cell t = gather t
  where gather (Cells cs) = concat <$> traverse gather cs
        gather (Cell name openL openR body) = (:[]) <$> cell name openL openR body
        gather t = fail $ "Non-cell term reachable from root: "++show t

-- hoist rewrites, but don't bring them past a nested cell
hoistRewrite :: Kast sort var -> RewriteItem (Kast sort var)
hoistRewrite t@Cell{} = Match t
hoistRewrite (KRewrite l r) = Change l r
hoistRewrite t =
  case plate hoistRewrite t of
    Match _ -> Match t -- Re-use current term if we can
    r@(Change _ _) -> r

-- hoist rewrites to enclosing cell.
hoistRewrites :: Kast sort VarId -> Kast sort VarId
hoistRewrites t@(Cell name openL openR body) =
  case hoistRewrite body of
    Change l r -> Cell name openL openR (KRewrite l r)
    Match _ -> t
hoistRewrites t = over plate hoistRewrites t

gatherRule :: (ConversionMonad i m) => Term -> m RuleBody
gatherRule = gatherCells (\name _ _ body ->
                           (,,) <$> cellCon name <*> cellSort name <*> pure (hoistRewrite body))

-- Need to be able to pick fresh vars...
closeCell :: (NameMonad m)
          => Sort -> Bool -> Kast () VarId -> Bool -> m (Kast () VarId)
closeCell _ False t False = return t
closeCell (Sort "K") False t True = kra t . Var () <$> nextVar
closeCell (Sort "K") True _ _ = fail $ "Cells of type K can't be open on the left"
closeCell (Sort "Map") _ t _ = (\wild -> MapUnion [t, Var () wild]) <$> nextVar
closeCell s _ _ _ = fail $ "Don't know how to close cells of sort "++show s

closeCells :: (NameMonad m, ConversionMonad i m) => Kast () VarId -> m (Kast () VarId)
closeCells =
  transformM (\t -> case t of
    Cell name openL body openR -> do
      bodySort <- cellSort name
      Cell name False False <$> closeCell bodySort openL openR body
    _ -> return t)

inferSort :: (ConversionMonad i m) => (Set Sort -> Set Sort) -> Set Sort -> m Sort
inferSort glb boundSorts =
  let adjust sort set =
        if Set.member sort set && Set.size set > 1
        then Set.delete sort set
        else set
      adjusted = adjust (Sort "K") boundSorts
  in case Set.toList (glb adjusted) of
    [] -> fail $ "InferSort - not sort consistent with all upper bounds in "++show boundSorts
    [s] -> return s
    sorts -> fail $ "InferSort - multiple maximal sorts "++show sorts
             ++" consistent with upper bounds "++show boundSorts

getInferSort :: (ConversionMonad i m) => m (Set Sort -> m Sort)
getInferSort = do
  glb <- getGLB
  return $ inferSort glb

sortTerms :: (Show var, Ord var, ConversionMonad i m)
          => [(Sort, Kast () var)] -> m [Kast Sort var]
sortTerms terms = do
  cellSorts <- getCellSorts
  labelSorts <- getLabelSorts
  inferSort <- getInferSort
  inferSorts' cellSorts labelSorts inferSort terms

-- | flatten any terms matching the prism
gather :: Prism' t [t] -> [t] -> [t]
gather con = go where go = concatMap (\t -> maybe [t] go (t ^? con))

-- | butLone applies the function except on singleton list.
butLone :: ([a] -> a) -> [a] -> a
butLone _ [x] = x
butLone f xs = f xs

reassocTerm :: Kast sort var -> Kast sort var
reassocTerm t = over plate reassocTerm $ case t of
  KSequence ts -> butLone KSequence (gather _KSequence ts)
  MapUnion ts ->  butLone MapUnion (gather _MapUnion ts)
  KList ts -> KList (gather _KList ts)
  t -> t

recognizeMapLabels :: (Show sort, Show var, ConversionMonad i m)
                   => Kast sort var -> m (Kast sort var)
recognizeMapLabels t = do
  hookInfo <- view convHooks
  let isHook h = (`Set.member` (hookInfo ^. ix h))
  return (recognizeMapLabelsByPred (isHook "Map:__") (isHook "Map:_|->_") (isHook "Map:.Map") t)

recognizeMapLabelsByPred :: (Show sort, Show var)
                         => (Label -> Bool) -> (Label -> Bool) -> (Label -> Bool)
                         -> Kast sort var -> Kast sort var
recognizeMapLabelsByPred isUnion isItem isEmptyMap = transform expandMap
  where expandMap (KApp _ (LCon l) t)
          | isUnion l = case t of
              KList ts -> MapUnion ts
              _ -> error $ "Map union label should only be used on explicit klist, not "++show t
          | isItem l = case t of
              KList [l,r] -> MapItem l r
              _ -> error $ "Map item label should only be used on 2-item klist, not "++show t
          | isEmptyMap l = case t of
              KList [] -> MapUnion []
              _ -> error $ ".Map label should only be used on empty klist, not "++show t
        expandMap t = t

recognizeBooleans :: (Show sort, Show var, ConversionMonad i m)
                  => Kast sort var -> m (Kast sort var)
recognizeBooleans t = do
  mbBoolSorts <- view (convSortHooks . at "Bool")
  let isBoolSort = case mbBoolSorts of
        Just sorts -> \s -> Set.member s sorts
        Nothing -> \s -> s == "#Bool"
  return (recognizeBooleansBySorts isBoolSort t)

recognizeBooleansBySorts :: (Show sort, Show var) => (Sort -> Bool) -> Kast sort var -> Kast sort var
recognizeBooleansBySorts isBoolSort = transform fixBoolTok
  where fixBoolTok t@(Token s val) | isBoolSort s = case val of
          "true" -> BoolToken s True
          "false" -> BoolToken s False
          _ -> error $ "Found boolean token with bad value "++show t
        fixBoolTok t = t


makeFreezers :: (Show sort, Show var) => Kast sort var -> Kast sort var
makeFreezers (KSequence ts) = KSequence (map makeFreezers' ts)
  where makeFreezers' (KSequence ts) = KSequence (map makeFreezers' ts)
        makeFreezers' t = case [h | h@(Hole _) <- universe t] of
          [] -> t
          [Hole s] -> Freezer s t
          _ -> error $ "Multiple holes in term "++show t
makeFreezers t = over plate makeFreezers t

ruleTerms :: Traversal (a,Maybe a) (b,Maybe b) a b
ruleTerms = beside id traverse

completeCells :: (ConversionMonad i m) => Kast sort var -> m (Kast sort var)
completeCells t@(KRewrite _ _) = pure $ Cell "k" False True t
completeCells t = pure t

ruleToClause :: (ConversionMonad i m) => String -> m (Maybe String, String)
ruleToClause r = do
  let (tm,condition,attrs) = parseRule r
      raw = (tm,condition)
  (renamed, nextFresh) <- flip runStateT (0::Int) $
      (ruleTerms numberWild >=> _1 (completeCells >=> closeCells)) raw
  (normBody, normSC) <- flip ruleTerms renamed $
     return . reassocTerm . hoistRewrites <=< recognizeMapLabels <=< recognizeBooleans
  (sorted:sortedSC') <- sortTerms ((Sort "K",normBody):
    [(Sort "Bool",sc) | sc <- maybeToList normSC])
  cellSorts <- getCellSorts
  let sortedSC = listToMaybe sortedSC'
      froze = makeFreezers sorted
  let (renamedTm, renamedSC)
         = renameVars (beside traverse (traverse . traverse)) (froze,sortedSC)
  gathered <- over (traverse ._3 . traverse) reassocTerm <$> gatherRule renamedTm
  convInfo <- getConvInfo
  return $ (getAttr "label" attrs, convertRule convInfo (Constructor "kstep") renamedSC gathered)

testCellInfo :: Map CellLabel (Constructor,Sort)
testCellInfo = Map.fromList $
  [(c,(Constructor con,Sort s)) | (c,con,s) <-
  [("k","k_cell","K")
  ,("env","env_cell","Map")
  ,("stk","stk_cell","Frames")
  ,("heap","heap_cell","Map")
  ,("funs","fun_cell","Map")
  ,("mark","mark_cell","Int")

  ,("state","state_cell","Map")
  ]]
testCellCons :: Map CellLabel Constructor
testCellCons = Map.map fst testCellInfo

testCellSorts :: Map CellLabel Sort
testCellSorts = Map.map snd testCellInfo

translateRules' :: ConversionInfo -> [String] -> Errored [String]
translateRules' coqInfo convRules = do
  let ruleInfo = RuleConversionInfo testCellSorts testCellCons coqInfo
  rules <- runReaderT (traverse ruleToClause convRules) ruleInfo
  return (mkClauses 0 rules)
 where mkClauses _ [] = []
       mkClauses ix ((label,decl):rules) =
         let (nextIx,name) = maybe (ix+1,"k_rule_"++show ix) (\l -> (ix,l)) label
         in (" | "++name++" : "++decl) : mkClauses nextIx rules

translateRules :: (Data def) => def -> Errored [String]
translateRules def = do
  coqInfo <- analyze def
  let rules = def ^.. template . _RuleItem
  translateRules' coqInfo rules

{-
parseSig :: String -> (String,String,[String])
parseSig str =
  let (name,ty) = splitType str
      (ret,args) = parseType [] ty
  in (name,ret,args)
 where splitType (':':':':ty) = ("",ty)
       splitType (c:cs) = let (name,ty) = splitType cs in (c:name,ty)
       splitType "" = error "End of string while looking for ::"
       parseType types ('-':'>':ret) = (ret,reverse types)
       parseType types ty = grabArg types "" ty
       grabArg types cur ('-':'>':ret) = (ret,reverse (reverse cur:types))
       grabArg types cur ('*':ty) = grabArg (reverse cur:types) "" ty
       grabArg types cur (c:ty) = grabArg types (c:cur) ty
       grabArg _ _ "" = error "End of string while reading argument type"
-}
