{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE OverloadedStrings #-}
module Terms where
import           Control.Applicative
import           Control.Lens hiding (from,to,cons)
import           Data.Data
import           Data.Foldable (Foldable)
import           Data.Traversable (sequenceA)
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Set (Set)
import           Data.String

import           Util.TwoStage

import           Grammar

data Var = Named String | Wild
  deriving (Show,Eq,Ord,Typeable,Data)
data VarId = UserVar String
           | GenVar Int
  deriving (Eq,Ord,Typeable,Data)
instance Show VarId where
  show (UserVar v) = v
  show (GenVar x) = '*':show x
instance IsString VarId where
  fromString = UserVar

-- Need ksequence, freezers
type Term = Kast Sort String
data KastLabel = LCon Label | LVar String
  deriving (Typeable, Data,Show)
data Kast sort var
  = Amb [Kast sort var] -- only for testing
  | KRewrite (Kast sort var) (Kast sort var)
  | Cells [Kast sort var]
  | Cell String Bool Bool (Kast sort var)
  | Token Sort String
  | BoolToken Sort Bool
  | KWrappedLabel Label
  | Annot (Kast sort var) Sort
  | KApp sort KastLabel (Kast sort var) -- should be a KList
  | KSequence [Kast sort var]
  | KList [Kast sort var]
  | MapUnion [Kast sort var]
  | MapItem (Kast sort var) (Kast sort var)
  | Var sort var
  | Freezer sort (Kast sort var) -- hole sort
  | Hole sort
  deriving (Show, Functor, Foldable, Traversable, Typeable, Data)
makePrisms ''Kast

instance Plated (Kast sort var) where
  plate f (Amb ts) = Amb <$> traverse f ts
  plate f (KRewrite l r) = KRewrite <$> f l <*> f r
  plate f (Cells cs) = Cells <$> traverse f cs
  plate f (Cell label openL openR body) =
    Cell label openL openR <$> f body
  plate _ t@(Token _ _) = pure t
  plate _ t@(BoolToken _ _) = pure t
  plate _ t@(KWrappedLabel _) = pure t
  plate f (Annot t s) = (\t' -> Annot t' s) <$> f t
  plate f (KApp s l t) = KApp s l <$> f t
  plate f (KSequence ts) = KSequence <$> traverse f ts
  plate f (KList ts) = KList <$> traverse f ts
  plate f (MapUnion ts) = MapUnion <$> traverse f ts
  plate f (MapItem k v) = MapItem <$> f k <*> f v
  plate _ t@(Var _ _) = pure t
  plate f (Freezer s t) = Freezer s <$> f t
  plate _ t@(Hole _) = pure t

labelApp :: Label -> sort -> [Kast sort var] -> Kast sort var
labelApp l s ts = KApp s (LCon l) (KList ts)

labelApp2 :: Label -> sort -> Kast sort var -> Kast sort var -> Kast sort var
labelApp2 l s t1 t2 = labelApp l s [t1,t2]

kra :: Kast a b -> Kast a b -> Kast a b
kra (KSequence ks1) (KSequence ks2) = KSequence (ks1++ks2)
kra (KSequence ks1) k2              = KSequence (ks1++[k2])
kra k1              (KSequence ks2) = KSequence ([k1]++ks2)
kra k1              k2              = KSequence [k1,k2]

type CellLabel = String

-- Various places complain we don't handle Amb, Rewrite, Cells, etc
-- Maybe make a more restricted type with those squeezed out?

termSort :: (Show var) => Kast Sort var -> Sort
termSort (KApp s _ _) = s
termSort (KSequence _) = Sort "K"
termSort (MapUnion _) = Sort "Map"
termSort (MapItem _ _) = Sort "Map"
termSort (Var s _) = s
termSort (Freezer _ _) = Sort "KItem"
termSort (Hole s) = s
termSort (Token s _) = s
termSort (BoolToken s _) = s
termSort t = error $ "Internal Error: Unexpected term in termSort: "++show t

-- freezer is kind of a binding construct

-- syntactic well-formedness, no sort checks
-- ensures that MapUnion/KSequence/Cells/KList are
-- not nested. Also allows MapUnion to contain
-- only MapItem and appropriately-typed variables
wfTerm :: Term -> Bool
wfTerm (KApp _ _ (KList ts)) = all wfTerm ts
wfTerm (KApp _ _ (Var (Sort "KList") _)) = True
wfTerm (KApp _ _ _) = False
wfTerm (MapUnion [_]) = False
wfTerm (KSequence ts) = all wfItem ts
  where wfItem (KSequence _) = False
        wfItem t = wfTerm t
wfTerm (MapUnion ts) = all wfItem ts
  where wfItem (MapItem _ _) = True
        wfItem (Var s _) = s == Sort "Map"
        wfItem _ = False
wfTerm (Cells ts) = all wfItem ts
  where wfItem (Cells _) = False
        wfItem t = wfTerm t
wfTerm (KList ts) = all wfItem ts
  where wfItem (KList _) = False
        wfItem t = wfTerm t
wfTerm (Cell _ _ _ t) = wfTerm t
wfTerm (MapItem k v) = wfTerm k && wfTerm v
wfTerm (Freezer _ t) = wfTerm t
wfTerm (Hole _) = True
wfTerm (Var _ _) = True
wfTerm (Token _ _) = True
wfTerm (BoolToken _ _) = True
wfTerm (KWrappedLabel _) = True
wfTerm (Annot t _) = wfTerm t
wfTerm (KRewrite l r) = wfTerm l && wfTerm r -- TODO: exclude rewrites
wfTerm (Amb _) = False

{- Infer sorts for many terms -}
-- TODO better error messages - somehow annotate the sort inference
-- pass so it has a nicer top level error message and stuff
inferSorts' :: (Ord var, Show var, Applicative m)
            => Map CellLabel Sort -- ^ cell sorts
            -> Map Label (Sort,[Sort]) -- ^ label sorts
            -> (Set Sort -> m Sort) -- ^ GLB function
            -> [(Sort,Kast () var)] -- ^ unsorted terms with context sorts
            -> m [Kast Sort var] -- ^ error or sorted terms
inferSorts' cellSorts labelSorts =
  solveIx (traverse . uncurry . assignSorts cellSorts labelSorts) . traverse

{- Infer sorts in a term, handling variables. -}
-- TODO: a version of sort inference integrated with
-- parsing and ambiguity resolution
inferSorts :: (Ord var, Show var, Applicative m)
           => Map CellLabel Sort -- ^ cell sorts
           -> Map Label (Sort,[Sort]) -- ^ label sorts
           -> (Set Sort -> m Sort) -- ^ GLB function
           -> Sort -- ^ target sort
           -> Kast () var
           -> m (Kast Sort var) -- ^ error or sorted term
inferSorts cellSorts labelSorts =
  auf (iso Indexed runIndexed) solveIx (assignSorts cellSorts labelSorts) . traverse

assignSorts :: (Ord var, Show var, Show s, Applicative f, Indexable Sort p)
            => Map CellLabel Sort -- ^ Cell sorts
            -> Map Label (Sort,[Sort]) -- ^ Label sorts
            -> (p var (f Sort)) -- ^ supplied variable sorts, as mapping from name to sort,
                                -- with optional access to the context sort
            -> Sort -- ^ top context sort
            -> Kast s var -- ^ term to sort
            -> f (Kast Sort var) -- ^ sorted term
assignSorts cellSorts labelSorts varSorts = go
  where go target@"K" t = wrapK <$> go' target t
          where wrapK t' = case t' of
                  KSequence _ -> t'
                  Var "K" _ -> t'
                  Cells _ -> t'
                  Cell _ _ _ _ -> t'
                  KRewrite _ _ -> t'
                  _ -> KSequence [t']
        go target t = go' target t

        go' target t = case t of
          KRewrite l r -> KRewrite <$> go target l <*> go target r
          Cells cs -> Cells <$> traverse (go target) cs
          Cell cellName openL openR body ->
            case Map.lookup cellName cellSorts of
              Just cellSort -> do
                (Cell cellName openL openR) <$> go cellSort body
              Nothing -> error $ "Unknown cell "++show cellName
          Token s v -> pure (Token s v)
          BoolToken s v -> pure (BoolToken s v)
          KWrappedLabel l -> pure (KWrappedLabel l)
          Annot body ann -> go ann body -- TODO: check subsorting
          KApp _ (LCon label) (KList args) ->
            case Map.lookup label labelSorts of
              Nothing -> error $ "No sort information for label "++show label
              Just (retSort,argSorts)
                | length argSorts == length args ->
                  -- TODO: check arg subsorting
                  KApp retSort (LCon label) . KList <$> sequenceA (zipWith go argSorts args)
                | otherwise -> error $ "Wrong number of arguments for "++show label
                                 ++" declared "++show argSorts++" applied to "++show args
          KApp _ _ _-> error $ "only handling KApp of label constant to klist, got "++show t
          KSequence ks -> let sorts = tail (replicate (length ks) "KItem"++["K"])
            in KSequence <$> sequenceA (zipWith go sorts ks)
          KList ks -> KList <$> traverse (go kSort) ks
          MapUnion ms -> MapUnion <$> traverse (go mapSort) ms
          MapItem k v -> MapItem <$> go kSort k <*> go kSort v
          Var _ v -> flip Var v <$> indexed varSorts target v
          Freezer _ body ->
            -- TODO: better error reporting here
            let wrapFreezer body' =
                  case [s | Hole s <- universe body'] of
                    [] -> error $ "No hole in freezer "++show t
                    [holeSort] -> Freezer holeSort body'
                    _ -> error $ "Multiple holes in freezer "++show t
            in wrapFreezer <$> go target body
          Hole _ -> pure (Hole target)
          Amb _ -> error "Can't sort terms with remaining ambiguities"
        kSort = Sort "K"
        mapSort = Sort "Map"
