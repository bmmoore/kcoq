{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module TypeAnalysis where
import           Control.Applicative
import           Control.Exception
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Char (isAlpha,isAlphaNum)
import           Data.Foldable (foldMap, traverse_)
import           Data.List (intercalate,(\\),isPrefixOf,nub,sort,foldl',find,partition)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (maybeToList,listToMaybe,fromMaybe,fromJust)
import           Data.Monoid
import           Data.Set (Set)
import qualified Data.Set as Set

import           Control.Lens
import           GHC.Generics (Generic)
import           Data.Data
import           Data.Set.Lens
import           Data.Data.Lens

import           Attributes
import           Definition
import           Grammar
import           Module

import           Data.Graph.Inductive.PatriciaTree
import           Data.Graph.Inductive hiding (empty,(&))
import qualified Data.Graph.Inductive as G
import           Data.Graph.Inductive.NodeMap as NM

import           BasicParser(basicParseFile,prod)

import           Debug.Trace

import           CoqConversion

type Errors f = (Applicative f, Monad f, NamingScheme, LabelScheme)
type Errored a = forall f . (Errors f) => f a

-- little utility stuff
traverseEitherWithKey :: (Applicative t) =>
  (k -> a -> t (Either b c)) -> Map k a -> t (Map k b, Map k c)
traverseEitherWithKey f m = fmap (Map.mapEither id) (Map.traverseWithKey f m)

getsGr :: (gr a b -> r) -> NodeMapM a b gr r
getsGr f = gets (f . snd)

modifyGr :: (gr a b -> gr a b) -> NodeMapM a b gr ()
modifyGr f = modify (\(n,g) -> (n,f g))

-- Starting conversion

syntaxProds :: (LabelScheme) => Syntax -> (Sort,(Attributes,[Production],[ListProduction]))
syntaxProds s = (syntaxSort s, (s ^. attributes, s ^.. template . filtered goodProd, s ^.. template))

goodProd p = not (badProd p)
badProd p = maybe False (`elem`badLabels) (prodLabel p)
  where badLabels = ["'#if_#then_#else_#fi"
                    ,"'isVariable(_)"
                    ]

gatherProds :: (Data def, LabelScheme) => def -> Map Sort (Attributes,[Production],[ListProduction])
gatherProds def = appEndo (def ^. template . to syntaxProds . to insert) Map.empty
 where insert (name,info) = Endo (Map.insertWith (<>) name info)

-- Interfere with super-special sorts like Map at this point.
-- Use Map.adjust to replace-if-present

data SortInfo = SortInfo
  {_sortAttrs :: Attributes
  ,_sortNormalLabels :: [Label]
  ,_sortTokenProds :: [Production]
  ,_sortSubsorts :: Map Sort Attributes
  }
 deriving (Show, Generic, Typeable, Data)
makeLenses ''SortInfo
instance HasAttributes SortInfo where
  attributes = sortAttrs

data ListSortInfo = ListSortInfo
 {_listSortAttrs :: Attributes
 ,_listSortProd :: ListProduction
 }
 deriving (Show, Generic, Typeable, Data)
makeLenses ''ListSortInfo
instance HasAttributes ListSortInfo where
  attributes = listSortAttrs

categorizeSort :: Sort -> (Attributes,[Production],[ListProduction])
  -> Errored (Map Label [Production], Either SortInfo ListSortInfo)
categorizeSort sortName (attrs, normProds, listProds) = do
  let tokenProds = [p | p@TokenProduction{} <- normProds]
  let classes@((badProds, funProds), (subsortProds, dataProds)) =
        normProds & partition isFunctionProd & both %~ partition isSubsorting
  when (not (null badProds)) $ fail $
    "Found subsort productions marked as hook or function "++show badProds
  let subsortInfo = Map.fromListWith (++) [(head (prodArgs p), p ^. attributes)
                                          | p <- subsortProds]
      byLabel prods = Map.fromListWith (++) [(l, [p]) | p <- prods, l <- maybeToList (prodLabel p)]
      dataInfo = byLabel dataProds
      funInfo = byLabel funProds
  let complainConflict (label,(dataProds, funProds)) = fail $ "Label "++show label
          ++" defined as both ordinary and data,"
          ++" respectively by productions "++show dataProds++" and "++show funProds
   in traverse_ complainConflict (Map.toList (Map.intersectionWith (,) dataInfo funInfo))
  let labelInfo = Map.union dataInfo funInfo
  case listProds of
    [] -> do
      return (labelInfo, Left (SortInfo attrs (Map.keys dataInfo) tokenProds subsortInfo))
    [lprod] -> do
      when (not (null dataProds)) $ fail $
        "Has list production, but also ordinary non-function productions "++
        show lprod++", "++show dataProds
      return (labelInfo, Right (ListSortInfo attrs lprod))
    lprods -> fail $ "Has multiple list sort productions "++show lprods

newtype Compose f g x = Compose {runCompose :: f (g x)}
  deriving (Functor)
instance (Applicative f, Applicative g) => Applicative (Compose f g) where
  pure x = Compose (pure (pure x))
  Compose f <*> Compose x = Compose (liftA2 (<*>) f x)

data DefinitionInfo = DefinitionInfo
  {_normalSortsInfo :: Map Sort SortInfo
  ,_listSortsInfo :: Map Sort ListSortInfo
  ,_labelInfo :: Map Label (Sort,[Production])
  }
 deriving (Show, Generic, Typeable, Data)
makeLenses ''DefinitionInfo

organizeProds :: Map Sort (Attributes,[Production],[ListProduction]) -> Errored DefinitionInfo
organizeProds sorts = do
  let item  sort sortInfo = Compose $
           (_1 %~ Endo . Map.unionWith (Map.unionWith (++)) . Map.map (Map.singleton sort))
          <$> categorizeSort sort sortInfo
  (elabelTables, (normalSorts, listSorts)) <- runCompose (traverseEitherWithKey item sorts)
  let labelTables = appEndo elabelTables Map.empty
  labelInfo <- flip Map.traverseWithKey labelTables $ \label prods ->
    case Map.toList prods of
      [(sort,prods)] -> pure (sort,prods)
      cases -> fail $ "Label "++show label++" defined in multiple sorts:\n"
               ++unlines (map show cases)
  return (DefinitionInfo normalSorts listSorts labelInfo)

mkDefinitionInfo :: (Data def) => def -> Errored DefinitionInfo
mkDefinitionInfo def = organizeProds (gatherProds (def, predefined))

dumpNormalSorts :: DefinitionInfo -> IO ()
dumpNormalSorts di = mapM_ print
  [(s, i ^. sortAttrs, i ^. sortNormalLabels, Map.toList (i ^. sortSubsorts))
  | (s,i) <- Map.toList (di ^. normalSortsInfo)]

dumpListSorts :: DefinitionInfo -> IO ()
dumpListSorts di = mapM_ print
  [(s, i ^. listSortAttrs, i ^. listSortProd)
  | (s,i) <- Map.toList (di ^. listSortsInfo)]

dumpLabelInfo :: DefinitionInfo -> IO ()
dumpLabelInfo di = mapM_ print . Map.toList $ di ^. labelInfo

dumpDefInfo :: DefinitionInfo -> IO ()
dumpDefInfo di = do
  putStrLn "Normal Sorts:"
  dumpNormalSorts di
  putStrLn "List Sorts:"
  dumpListSorts di
  putStrLn "Label Info:"
  dumpLabelInfo di

predefined :: [Syntax]
predefined = [Syntax "KItem" [Attribute "coq" "kitem"] []
             ,Syntax "K" [Attribute "coq" "k"] []
             ,Syntax "Map" [Attribute "hook" "Map"] []
             ]
-- Extracting which sorts are strict
-- TODO: nice error handling
strictPositions :: [Sort] -> String -> [Sort]
strictPositions sorts "" = sorts
strictPositions sorts positions =
  let readInt w = case reads w of
        [(i,"")] -> i
        _ -> error $ ("Word "++show w++" is not an integer in strictness arguments "++show positions)
      indices = map readInt (words positions)
      valid = [1..length sorts]
  in case find (not . (`elem`valid)) indices of
    Just invalid -> error $ "Index "++show invalid++" out of range in stricness attribute"
    Nothing -> map ((sorts !!) . (subtract 1)) indices

strictSorts :: Fold Production Sort
strictSorts f p = ( folding (getAttrs "strict" <> getAttrs "seqstrict")
                   . folding (strictPositions (prodArgs p))) f p

-- Which sorts may be replaced by KResult as evalution proceeds.
-- Approximated as sorts appearing in "strict" positions,
-- plus anything marked with a special "coqEvaluated" attribute
getValueSorts :: DefinitionInfo -> [Sort]
getValueSorts =
  Set.toList . setOf (template . strictSorts
    <> normalSortsInfo . itraversed . filtered (hasAttr "coqEvaluated") . asIndex)

getAllSorts :: DefinitionInfo -> [Sort]
getAllSorts di = Set.toList (di ^. (normalSortsInfo . to Map.keysSet
                                    <> listSortsInfo . to Map.keysSet))

-- Graph edges point always from the supersort to the subsort.

-- Initialize a graph from declared subsorts.
initSortGraph :: [Sort] -> Map Sort (Map Sort Attributes) -> NodeMapM Sort Attributes Gr ()
initSortGraph allSorts subsorts = do
  insMapNodesM allSorts
  insMapEdgesM [ (super, sub, attrs)
               | (super, subs) <- Map.toList subsorts
               , (sub, attrs) <- Map.toList subs
               ]

{- $subsorting.
  For proper implementation of subsorting, we should generate
  data types and injection functions so there is only one
  way any sort will end up wrapped into a supersort.
  If multiple immediate children of a sort have a common
  subsort, we may need a constructor for directly injecting
  that subsort to preserve uniqueness.
  To be precise, if the supersort is the immediate
  dominator (with respect to itself as root) of another
  sort that isn't directly subsorted into the parent sort,
  then we need to add a direct relationship.

  Considering cases, adding this edge can't change
  whether any other pair of sorts are in this relationship
  (B is immediate dominator with respect to B of Y
  and there is no edge Y), so we can just find and add
  them all.

  As a preprocessing step, we can minimize the
  graph by finding and deleting any edge A -> C
  where A < B < C for some intermediate node.
  These are again independent, as the condition mentions
  only reachability, and deleting such an edge
  preserves reachability.
 -}
-- TODO: more general handling of union sorts.
addKItemSubsorts :: NodeMapM Sort Attributes Gr ()
addKItemSubsorts = do
  gr <- gets snd
  special@[k,kitem] <- mkNodesM ["K","KItem"]
  let existingKItem = suc gr (fst kitem)
      missingKItem = nodes gr \\ (map fst special++existingKItem)
  modifyGr (insEdges [(fst kitem,m,[]) | m <- missingKItem])

addKResultSubsorts :: [Sort] -> NodeMapM Sort Attributes Gr ()
addKResultSubsorts valueSorts = do
  (kresult,_) <- mkNodeM "KResult"
  valueNodes <- mkNodesM valueSorts
  modifyGr (mergeEdges [(v,kresult,[]) | (v,_) <- valueNodes])

distributeNodes :: (DynGraph g, Monoid b) => [Node] -> g a b -> g a b
distributeNodes [] g = g
distributeNodes (n:ns) g =
  case match n g of
    (Nothing,_) -> distributeNodes ns g
    (Just ctx@(before,_,_,after),g') ->
      let g'' = mergeEdges [(b,a,mempty) | (_,b) <- before, (_,a) <- after] g'
      in ctx G.& (distributeNodes ns g'')

distributeUnionSorts :: [Sort] -> NodeMapM Sort Attributes Gr ()
distributeUnionSorts unionSorts = do
  unionNodes <- map fst <$> mkNodesM unionSorts
  modifyGr (distributeNodes unionNodes)

hasEdge :: (Graph g) => g a b -> Node -> Node -> Bool
hasEdge g super sub = sub `elem` suc g super

mergeAdj :: (Monoid b) => Node -> b -> Adj b -> Adj b
mergeAdj k v [] = [(v,k)]
mergeAdj k v (hd@(v',k'):assocs)
  | k == k' = (v' <> v,k'):assocs
  | otherwise = hd:mergeAdj k v assocs

mergeEdge :: (DynGraph g, Monoid b) => LEdge b -> g a b -> g a b
mergeEdge (from,to,l) g = (pred,from,labFrom,mergeAdj to l suc) G.& g'
  where (Just (pred,_,labFrom,suc),g') = match from g

mergeEdges :: (DynGraph g, Monoid b) => [LEdge b] -> g a b -> g a b
mergeEdges edges g = foldl' (flip mergeEdge) g edges

simplifyDAG :: (DynGraph gr) => gr a b -> gr a b
simplifyDAG graph =
  let reachable = trc graph
      twoStep super sub = any (\mid -> mid /= sub && hasEdge reachable mid sub) (suc graph super)
      redundant = [e | e@(super,sub) <- edges graph, twoStep super sub]
  in delEdges redundant graph

{- | Ensure there is a direct edge between a pair of sorts that
     are related by multiple disjoint paths through the subsorting
     graph. Translating this to a constructor gives us a preferred
     wrapper for implementing that subsorting.

     Even after this completion, some subsorting relationship must
     be implemented by functions that rewrap certain injections,
     but with these added injections that's only the case for
     injecting/projecting a sort A to/from B where some immediate
     subsorts of B are also descendants of A.

     The implementation works by finding for each node all the other
     nodes whose immediate dominator with respect to the current parent
     is the current parent itself, and adding edges if there is not already
     an immediate edge.
 -}
completeDAG :: (DynGraph gr, Monoid b) => b -> gr a b -> gr a b
completeDAG label graph =
  let allNodes = nodes graph
      neededEdges = [(super,sub,label)
                    | super <- allNodes
                    , (sub,idom) <- iDom graph super
                    , idom == super]
  in mergeEdges neededEdges graph

prepareSubsortGraph :: DefinitionInfo -> (NodeMap Sort, Gr Sort Attributes)
prepareSubsortGraph d =
  let sortMap = Map.map (^. sortSubsorts) (d ^. normalSortsInfo)
      allSorts = getAllSorts d
      valueSorts = getValueSorts d
  in snd . run G.empty $ do
    initSortGraph allSorts sortMap
    addKItemSubsorts
    -- modifyGr simplifyDAG -- TODO: see if this interferes with KResult handling anymore
    addKResultSubsorts valueSorts
    distributeUnionSorts ["KResult"]
    modifyGr (completeDAG [])

nameFromAttrs :: (HasAttributes attrs, Errors f)
              => attrs -> f Constructor -> ([String] -> f Constructor) -> f Constructor
nameFromAttrs attrs ifNone ifMany = case nub (getAttrs "coq" attrs) of
  [] -> ifNone
  [name] -> pure (conFromAttr name)
  names -> ifMany names

nameSubsort :: Sort -> Sort -> Attributes -> Errored (Maybe Constructor)
nameSubsort _ "KResult" _ = pure Nothing
nameSubsort super sub attrs = Just <$> nameFromAttrs attrs
  (pure (conForSubsortProd super sub))
  (\names ->fail $ "Conflicting coq names given for subsorting of "
              ++show sub++" into "++show super++": "++unwords names)

{- *** Old graph stuff -}

pickInjections :: (NamingScheme)
               => Map Sort (Map Sort (Maybe Constructor))
               -> Map (Sort,Sort) Injection
pickInjections injectionTable =
  Map.fromList [((sub, super), inj)
               | (super, subs) <- Map.toList injectionTable
               , (sub, mbCon) <- Map.toList subs
               , let injFun = InjFunctions (conInjFun sub super) (conProjFun sub super) mbCon
                     -- We generate a function if any immediate subtypes of sub
                     -- are also immediate subtypes of super. Should be fancier, eventually
                     inj = case mbCon of
                       Nothing -> injFun
                       Just c ->
                         case Map.lookup sub injectionTable of
                           Nothing -> error "Internal compiler error"
                           Just subsubs ->
                             if Map.null (Map.intersection subsubs subs)
                             then InjConstructor c else injFun
               ]

mkInjectionGraph :: Map (Sort,Sort) Injection -> NodeMapM Sort Injection Gr ()
mkInjectionGraph injectionTable = do
  insMapNodesM [n | (s,t) <- Map.keys injectionTable, n <- [s,t]]
  insMapEdgesM [(sub,super,inj) | ((sub,super),inj) <- Map.toList injectionTable]

-- | Creates all paths that use only transKeys as intermediate nodes
reflexiveTransitiveClosure :: (Ord k, Monoid a, Eq a)
                           => ((k,k) -> a -> a -> a) -> Map (k,k) a -> [k] -> [k] -> Map (k,k) a
reflexiveTransitiveClosure joinPaths initialEdges allKeys transKeys =
    let reflexivity = Map.fromList [((k,k),mempty) | k <- allKeys]
        closed = foldl' (transOn joinPaths allKeys) initialEdges transKeys
    in Map.unionWithKey joinPaths closed reflexivity

transOn :: (Ord k, Monoid a, Eq a)
                           => ((k,k) -> a -> a -> a) -> [k] -> Map (k,k) a -> k -> Map (k,k) a
transOn joinPaths allKeys edges k = Map.unionWithKey joinPaths edges
      (Map.fromListWithKey joinPaths
         [((k1,k2),e1 <> e2)
         | k1 <- allKeys
         , e1 <- maybeToList (Map.lookup (k1,k) edges)
         , k2 <- allKeys
         , e2 <- maybeToList (Map.lookup (k,k2) edges)
         ])

minOn :: (Ord b) => (a -> b) -> a -> a -> a
minOn f x y = if f x <= f y then x else y

{- | Take closure and build injection table.

   Keeps the shortest path between any pair of sorts,
   according to a lexicographic order that first minimizes
   the number of functions not backed by a wrapper.

   This should be unique/canonical after "completing"
   the graph.
 -}
mkInjections :: Map (Sort,Sort) Injection
             -> [Sort]
             -> Map (Sort,Sort) [Injection]
mkInjections oneStepInjections allSorts =
    reflexiveTransitiveClosure joinInj
      (Map.map (:[]) oneStepInjections)
      allSorts allSorts
  where joinInj (from,to) i1 i2 = minOn weight i1 i2
        weight injs = (length [() | InjFunctions _ _ Nothing <- injs]
                      ,length injs)

prettyGraph g =
  unlines $ flip concatMap (G.nodes g) $ \nodeIx ->
    [ show (lab_ nodeIx)++" => "++show [(lab_ s, label) | (s,label) <- G.lsuc g nodeIx]
    , show (lab_ nodeIx)++" <= "++show [(lab_ s, label) | (s,label) <- G.lpre g nodeIx]
    ]
 where lab_ n = fromJust (G.lab g n)

computeSubsorting :: DefinitionInfo -> Errored (Map (Sort,Sort) [Injection]
                                               ,Map Sort (Map Sort (Maybe Constructor))
                                               ,Gr Sort Injection)
computeSubsorting di = do
  let allSorts = Set.toList (di ^. (normalSortsInfo . to Map.keysSet
                                    <> listSortsInfo . to Map.keysSet))
      g = snd (prepareSubsortGraph di)
      lab_ n = fromJust (lab g n)
  -- traceM (prettyGraph g)
  subsortMap <-
    Map.traverseWithKey (\from -> Map.traverseWithKey (nameSubsort from))
      $ Map.fromList [(lab_ from, Map.fromList [(lab_ to,attrs) | (to,attrs) <- lsuc g from])
                        | from <- nodes g]
  -- traceM (unlines (map show (Map.toList subsortMap)))
  let oneStepInjectionTable = pickInjections subsortMap
      injections = mkInjections oneStepInjectionTable allSorts
      injectionGraph = run_ G.empty (mkInjectionGraph  oneStepInjectionTable)
      result = (injections,subsortMap,injectionGraph)
  -- traceM ("Result injections:\n"++unlines (map show (Map.toList injections)))
  -- traceM ("Result subsortMap:\n"++unlines (map show (Map.toList subsortMap)))
  -- traceM ("Result injectionGraph:\n"++prettyGraph injectionGraph)
  return result

{- *** End of old graph stuff -}


-- | Information needed for any of inference, rule generation, and syntax generation
data ConversionInfo = ConversionInfo
  { {- *** For type inference alone -}
   _convLabelSorts :: Map Label (Sort, [Sort])
   -- ^ Sort information for anything with a label.
    {- *** For term translation -}
  ,_convLabelConstructors :: Map Label Constructor
   -- ^ Map labels to Coq constructor/function. Needs to include functions.
  ,_convLabelIsFunction :: Map Label Bool
    -- ^ Tell if labels are functions, so we can skip/specialize translation
    -- of function-defining rules
  ,_convInjectionTable :: Map (Sort,Sort) [Injection]
   -- ^ Table of composed injection paths, key is (subsort,supersort)
  ,_convSortHoles :: Map Sort Constructor
   -- ^ Coq name to use as hole of given sort. Already reflected in convSortExtraCons
  ,_convSortTokens :: Map Sort Constructor
   -- ^ Coq name to use as token of given sort. Already reflected in convSortExtraCons
    {- *** For data type generation. Depends on everything above -}
  ,_convSortMap :: Map Sort CoqTerm
   -- ^ type translation for all sorts, including hooked and builtin sorts
  ,_convSortNormalProds :: Map Sort [Label]
   -- ^ List of the syntax formers for every non-hooked normal sort
  , _convSortExtraCons :: Map Sort [(Constructor,[Sort])]
   -- ^ names and arguments of extra constructors. Used to add holes, freezers, and tokens.
  ,_convSubsortGraph :: Map Sort (Map Sort (Maybe Constructor))
   -- ^ Maps supersort to table of direct subsorts labeled with Coq wrapper name
   -- should have an entry for every normal sort, even if it's empty
  ,_convOneStepInjectionGraph :: Gr Sort Injection
   -- ^ Direct subsorts represented as an fgl graph, oriented from subsort to supersort,
   -- for topological sorting and stuff
  ,_convHooks :: Map String (Set Label)
   -- ^ Map strings to declared labels with that hook.
  ,_convSortHooks :: Map String (Set Sort)
   -- ^ Map hook string to declared sorts with that hook
  }
  deriving (Show)
makeClassy ''ConversionInfo

type MakesLabelInfo a = Label -> (Sort,[Production]) -> Errored a
mkSig :: MakesLabelInfo (Sort,[Sort])
mkSig label (sort,prods) = (,) sort <$> case nub (map prodArgs prods) of
    [sig] -> return sig
    sigs -> fail $ "Label "++show label++" in sort "++show sort
            ++" has different arguments in different productions "++show prods

mkCon :: MakesLabelInfo Constructor
mkCon label (_, prods) = nameFromAttrs (prods ^. traverse . attributes)
  (pure (conFromLabel label))
  (\names -> fail $ "Label "++show label++" has conflicting coq attributes: "++unwords names)

mkLabelInfo :: DefinitionInfo -> Errored (Map Label (Sort,[Sort])
                                         ,Map Label Constructor)
mkLabelInfo di = do
  let listLabelInfo = Map.fromList . concat $
        [[(listProdSepLabel lsort lprod,((lsort,[listProdElement lprod,lsort]),"cons"))
         ,(Label ('.':show lsort),((lsort,[]),"nil"))]
        | (lsort, linfo) <- Map.toList (di ^. listSortsInfo)
        , let lprod = linfo ^. listSortProd]
  labelSorts <- itraverse mkSig (di ^. labelInfo)
  labelCons <- itraverse mkCon (di ^. labelInfo)
  return (Map.union (Map.map fst listLabelInfo) labelSorts
         ,Map.union (Map.map snd listLabelInfo) labelCons)

data SortTranslationOptions = SortTranslationOptions
  {predefinedSorts :: Map Sort CoqTerm
  ,hookTranslations :: Map String CoqTerm
  }

-- TODO: complain if it's both predefined and hooked
-- maybe warn earlier about conflicting options?
getCoqSort :: (HasAttributes attrs) =>  SortTranslationOptions
           -> Sort -> attrs -> Errored CoqTerm
getCoqSort options sort _attrs
  | Just name <- Map.lookup sort (predefinedSorts options) = pure name
getCoqSort options sort attrs =
  case (nub (getAttrs "hook" attrs), nub (getAttrs "coq" attrs)) of
    ([],[]) -> pure (ConApp (conFromSort sort) [])
    ([hook],[]) -> case Map.lookup hook (hookTranslations options) of
        Nothing -> fail $ "Unknown hook "++hook++" on sort "++show sort
        Just coqType -> pure coqType
    ([],[coqType]) -> pure (ConApp (conFromAttr coqType) [])
    (hooks,[]) -> fail $ "Multiple hooks for sort "++show sort++":"++unwords hooks
    ([],coqTypes) -> fail $ "Multiple coq attributes for sort "++show sort++":"++unwords coqTypes
    (hooks,coqTypes) -> fail $ "Sort "++show sort
      ++" has hook"++(case hooks of [hook] -> " "++hook; hooks -> "s "++unwords hooks)
      ++" and coq attribute"++(case coqTypes of [coq] -> " "++coq; coqs -> "s "++unwords coqs)
      ++" but should have at most one, total"

mkSortNames :: SortTranslationOptions -> DefinitionInfo -> Errored (Map Sort CoqTerm)
mkSortNames sortOpts di = do
  normalSortMap <- itraverse (getCoqSort sortOpts) (di ^. normalSortsInfo)
  let listElementMap = Map.map (listProdElement . view listSortProd) (di ^. listSortsInfo)
  listSortMap <- flip itraverse listElementMap $ \listSort elt ->
    case Map.lookup elt normalSortMap of
      Just eltCon -> pure (app1 "list" eltCon)
      Nothing -> fail $ "Could not find coq type for element sort "++show elt
                     ++" to assign coq sort for list sort "++show listSort
  return (Map.union normalSortMap listSortMap)

isNativeSort :: (HasAttributes info) => SortTranslationOptions -> Sort -> info -> Bool
isNativeSort sortOpts sortName attrs =
  (hasAttr "hook" attrs || Map.member sortName (predefinedSorts sortOpts))

mkConversionInfo :: SortTranslationOptions -> DefinitionInfo -> Errored ConversionInfo
mkConversionInfo sortOpts di = do
  let allSorts = getAllSorts di
      valueSorts = getValueSorts di
      holeInfo = Map.fromList [(s, conForHole s) | s <- valueSorts]
      freezerInfo = Map.singleton "KItem" [(conForFreezer, ["KItem"])]
      tokenInfo = Map.fromList [(s, conForToken s)
                               | (s,info) <- Map.toList (di ^. normalSortsInfo)
                               , not (null (info ^. sortTokenProds))]
      hasFunctionProds = Map.map (\(_,prods) -> any isFunctionProd prods) (di ^. labelInfo)
      extraCons = Map.unionsWith (++) [Map.map (\con -> [(con,["#String"])]) tokenInfo,
                                       freezerInfo,
                                       Map.map (\hole -> [(hole,[])]) holeInfo]
      normalLabels = Map.map (view sortNormalLabels)
                   . Map.filterWithKey (\sort info -> not (isNativeSort sortOpts sort info))
                   $ (di ^. normalSortsInfo)
      hookInfo = Map.fromListWith Set.union
                 [(hook, Set.singleton label)
                 | (label, (_,prods)) <- Map.toList (di ^. labelInfo)
                 , prod <- prods
                 , hook <- getAttrs "hook" prod
                 ]
      sortHookInfo = Map.fromListWith Set.union
                 [(hook, Set.singleton sort)
                 | (sort,hooks) <-
                     let sortsHooks lens = Map.toList (di ^. lens . to (Map.map (getAttrs "hook")))
                     in sortsHooks normalSortsInfo ++ sortsHooks listSortsInfo
                 , hook <- hooks]
  (\(labelSigs,labelCons) sortNames (injectionsTable, subsortTable, subsortGraph)->
     ConversionInfo labelSigs labelCons hasFunctionProds injectionsTable
       holeInfo tokenInfo sortNames normalLabels extraCons subsortTable subsortGraph
       hookInfo sortHookInfo)
    <$> mkLabelInfo di
    <*> mkSortNames sortOpts di
    <*> computeSubsorting di

defaultSortTranslationOptions = SortTranslationOptions predefinedSorts sortHooks
  where
    -- | Map from hooks to Coq sort names.
    sortHooks :: Map String CoqTerm
    sortHooks = Map.fromList
      [("Int",ConApp "Z" [])
      ,("Id",ConApp "string" [])
      ,("Bool",ConApp "bool" [])
      ,("Map",ConApp "Map" [ConApp "k" [], ConApp "k" []] )
      ]

    predefinedSorts :: Map Sort CoqTerm
    predefinedSorts = Map.fromList
      [("K",ConApp "k" []) -- The type K itself should get no productions.
      ,("#Bool",ConApp "bool" [])
      ,("#Float",ConApp "float" [])
      ,("#Int",ConApp "Z" [])
      ,("#String",ConApp "string" [])
      ]

analyze :: (Data def) => def -> Errored ConversionInfo
analyze = mkDefinitionInfo >=> mkConversionInfo defaultSortTranslationOptions
