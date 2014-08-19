{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module TypeConversion where
import           Control.Applicative
import           Control.Exception
import           Data.List (intercalate,(\\),isPrefixOf,nub,sort,foldl',find)
import           Data.Char (isAlpha)
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import           Data.Maybe (maybeToList,listToMaybe,fromMaybe,catMaybes,fromJust,mapMaybe)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.Monoid
import           Control.Monad.State hiding (mapM)
import           Data.Foldable (foldMap)
import           Data.Traversable (mapM)


import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)
import           Data.Data (Typeable,Data)
import           GHC.Generics (Generic)

import           Control.Lens

import           Definition
import           Module
import           Grammar
import           Attributes

import           BasicParser (kdef)
import           Text.Parsec (parse,eof)
import           KastParser
import           Terms

import           Prelude hiding (mapM)
import           Control.Monad.Reader hiding (mapM)

import           Data.Graph.Inductive(lab,lsuc,nodes,delNode)
import           Data.Graph.Inductive.PatriciaTree(Gr)
import           Data.Graph.Inductive.Query.DFS(topsort)
import           CoqConversion hiding (convLabels,convInjections,convFreezers,convHoles)
import           TypeAnalysis

import Debug.Trace

type ConversionMonad m = (Monad m, Applicative m, MonadReader ConversionInfo m, NamingScheme)

infoHelper :: (MonadReader s m) => Getting (First b) s b -> String -> m b
infoHelper lens msg = preview lens >>= maybe (fail msg) return

convSort :: (ConversionMonad m) => Sort -> m CoqTerm
convSort s = infoHelper (convSortMap . ix s)
  ("No Coq name found for sort "++show s)
convLabel :: (ConversionMonad m) => Label -> m Constructor
convLabel l = infoHelper (convLabelConstructors . ix l)
  ("No Coq name found for label "++show l)
labelSort :: (ConversionMonad m) => Label -> m (Sort, [Sort])
labelSort l = infoHelper (convLabelSorts . ix l)
  ("No sort information found for label "++show l)
sortDataLabels :: (ConversionMonad m) => Sort -> m [Label]
sortDataLabels s = infoHelper (convSortNormalProds . ix s)
  ("No production information found for sort "++show s)
sortHoles :: (ConversionMonad m) => Sort -> m (Maybe Constructor)
sortHoles s = view (convSortHoles . at s)
sortExtraCons :: (ConversionMonad m) => Sort -> m [(Constructor, [Sort])]
sortExtraCons s = infoHelper (convSortExtraCons . at s . to (maybe [] id))
  ("No information on special productions found for sort "++show s)
convNormalSorts :: (ConversionMonad m) => m [Sort]
convNormalSorts = view (convSortNormalProds . to Map.keys)
convSubsorts :: (ConversionMonad m) => Sort -> m (Map Sort (Maybe Constructor))
convSubsorts s = infoHelper (convSubsortGraph . ix s)
  ("No subsorts found for sort "++show s)
convInjection :: (ConversionMonad m) => Sort -> Sort -> m [Injection]
convInjection from to = infoHelper (convInjectionTable . ix (from,to))
  ("No injection found from "++show from++" to "++show to)
checkInjection :: (ConversionMonad m) => Sort -> Sort -> m (Maybe [Injection])
checkInjection from to = view (convInjectionTable . at (from,to))
oneStepInjectionGraph :: (ConversionMonad m) => m (Gr Sort Injection)
oneStepInjectionGraph = view convOneStepInjectionGraph

-- TODO: probably shouldn't count a hole, if that's somehow the only
-- proper constructor added to a sort
sortLacksProductions :: (ConversionMonad m) => Sort -> m Bool
sortLacksProductions s = null <$> sortDataLabels s

isSubsort :: (ConversionMonad m) => Sort -> Sort -> m Bool
isSubsort sub super
  | sub == super = pure True
  | otherwise = Map.member sub <$> convSubsorts super

labelArgs :: (ConversionMonad m) => Label -> m [Sort]
labelArgs = fmap snd . labelSort

fmtMatchFun :: Constructor -> CoqTerm -> CoqTerm
            -> [(CoqTerm -> CoqTerm, CoqTerm -> CoqTerm)]
            -> Maybe (CoqTerm -> CoqTerm) -> String
fmtMatchFun funName srcTy resTy clauses defaultClause =
  let srcVar = CoqVar (UserVar "x")
      matchVar = CoqVar (UserVar "i")
  in "Definition "++show funName++" (x : "++show srcTy++") : "++show resTy++" :=\n"
  ++ "  match x with\n"
  ++ unlines ["  | "++show (from matchVar)++" => "++show (to matchVar) | (from,to) <- clauses]
  ++ maybe "" (\t -> "  | _ => "++show (t srcVar)++"\n") defaultClause
  ++ "  end."

{- Makes injection into K.
   For a sort with subsorts, this consists of
   recursively invoking the injections on those sorts,
   and a catch-all case that wraps everything else
   in the appropriate K constructor otherwise.
 -}
mkInjection :: (ConversionMonad m) => Sort -> Sort -> m String
mkInjection src tgt = do
  tyName <- convSort src
  tgtName <- convSort tgt
  -- for every subsort of the source type, wrap it in the appropriate injection
  let clause (sub,Just con) = (\inj -> Just (app1 con, inject inj)) <$> convInjection sub tgt
      clause (sub,Nothing) = pure Nothing
  clauses <- liftM catMaybes . mapM clause . Map.toList =<< convSubsorts src
  catchAll <- do
    skipCatchAll <- sortLacksProductions src
    if skipCatchAll then return Nothing else Just . injectRigid <$> convInjection src tgt
  return $ fmtMatchFun (conInjFun src tgt) tyName tgtName
    clauses
    catchAll

mkProjection :: (ConversionMonad m)
              => Sort -> Sort -> m String
mkProjection src tgt = do
  srcName <- convSort src
  tgtName <- convSort tgt
  tsubs <- convSubsorts tgt
  skipDefault <-
     (&&) <$> sortLacksProductions tgt
          <*> (and <$> mapM (\tsub -> isSubsort tsub src) (Map.keys tsubs))
  let clause (tsub,Nothing) = pure Nothing
      clause (tsub,Just tcon) =
        fmap (\injpath -> (app1 tcon, app1 "Some" . inject injpath)) <$> checkInjection tsub src
  clauses <- catMaybes <$> mapM clause (Map.toList tsubs)
  return $ fmtMatchFun (conProjFun src tgt) tgtName (app1 "option" srcName)
    clauses (const (ConApp "None" []) <$ guard (not skipDefault))

-- TODO: move type representations and pretty-printing in CoqConversion
data ConDecl ty = ConDecl Constructor [ty]
  deriving (Show,Functor,Foldable,Traversable,Typeable,Data,Generic)

fmtConDecl :: CoqTerm -> ConDecl CoqTerm -> String
fmtConDecl result (ConDecl con args) =
  show con++" : "++foldr (\a r -> show a++" -> "++r) (show result) args

fmtInductive :: CoqTerm -> [ConDecl CoqTerm] -> [String]
fmtInductive name constructors = (show name++" : Set :="):
  prefix ("   "++) (" | "++) (map (fmtConDecl name) constructors)

mkInductive :: (ConversionMonad m)
            => Sort -> [ConDecl Sort] -> m [String]
mkInductive name constructors =
  fmtInductive <$> convSort name <*> (traverse . traverse) convSort constructors

prefix pfFirst pfRest (first:rest) = (pfFirst first):(map pfRest rest)
prefix _ _ [] = []

mkType :: (ConversionMonad m) => Sort -> m [String]
mkType sort = mkInductive sort =<<
  (\sub plain extra -> sub ++ plain ++ extra)
    <$> mkSubsortCons <$> convSubsorts sort
    <*> (traverse mkConstructor =<< sortDataLabels sort)
    <*> (map (uncurry ConDecl) <$> sortExtraCons sort)
 where mkSubsortCons = mapMaybe (\(sub,mbCon) -> flip ConDecl [sub] <$> mbCon) . Map.toList
       mkConstructor l = ConDecl <$> convLabel l <*> labelArgs l

mkTypes :: (ConversionMonad m)
        => [Sort] -> m [String]
mkTypes nonHookedSorts = do
  types <- mapM mkType nonHookedSorts
  let kdecl = ["k : Set := kdot | kra : kitem -> k -> k"]
  return (concat (prefix (prefix ("Inductive "++) id)
                         (prefix ("with "++) id)
                    (types++[kdecl]))
          ++[" ."])

mkAll :: (ConversionMonad m) => m [String]
mkAll = do
  sorts <- convNormalSorts
  dataDecl <- mkTypes sorts
  injectionGraph' <- oneStepInjectionGraph
  let injectionGraph =
        case [n | n <- nodes injectionGraph', lab injectionGraph' n == Just "K"] of
          [knode] -> delNode knode injectionGraph'
          [] -> injectionGraph'
  injections <- fmap (concat . concat) $
    forM (topsort injectionGraph) $ \srcId ->
     forM (lsuc injectionGraph srcId) $ \(tgtId,inj) ->
       case inj of
         InjConstructor _ -> return []
         InjFunctions _ _ _ -> do
           let lab_ = fromJust . lab injectionGraph
           inj <- mkInjection (lab_ srcId) (lab_ tgtId)
           proj <- mkProjection (lab_ srcId) (lab_ tgtId)
           return [inj,proj]
  return (dataDecl++[""]++injections)

translateSyntax :: (Data def) => def -> Errored [String]
translateSyntax = analyze >=> runReaderT mkAll
