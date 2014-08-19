{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE OverloadedStrings #-}
module CoqConversion where
import           Control.Applicative
import           Control.Lens hiding (from,to,cons)
import           Control.Monad.RWS
import           Data.Char (isDigit,isAlpha,isAlphaNum)
import           Data.Data (Data, Typeable)
import           Data.Foldable (Foldable,toList,foldMap)
import           Data.List (nub,(\\),partition,intersperse)
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.Maybe (fromMaybe)
import           Data.String (IsString(..))

import           Util.Zencode
import           Util.TwoStage

import           Grammar
import           Terms

{-|
 This module defines a partial syntax of Coq terms,
 and a translation from processed rules into them.
 -}

-- something with a unique supply for vars..
newtype OutVar = OutVar String
  deriving (Eq,Ord)
instance Show OutVar where
  show (OutVar v) = v
instance IsString OutVar where
  fromString = OutVar

-- | Coq identifiers.
-- The IsString instance should only be used for literals
-- of well-known Coq-size values like list.
newtype Constructor = Constructor String
  deriving (Eq,Ord,Typeable,Data)
instance (Show Constructor) where
  show (Constructor c) = c
instance IsString Constructor where
  fromString = Constructor

type NamingScheme =
  (?conForFreezer :: Constructor
  ,?conFromLabel :: Label -> Constructor
  ,?conFromSort :: Sort -> Constructor
  ,?conFromAttr :: String -> Constructor
  ,?conForHole :: Sort -> Constructor
  ,?conForToken :: Sort -> Constructor
  ,?conForSubsortProd :: Sort -> Sort -> Constructor
  ,?conInjFun :: Sort -> Sort -> Constructor
  ,?conProjFun :: Sort -> Sort -> Constructor
  )
conFromLabel :: (NamingScheme) => Label -> Constructor
conFromLabel = ?conFromLabel
conFromSort :: (NamingScheme) => Sort -> Constructor
conFromSort = ?conFromSort
conFromAttr :: (NamingScheme) => String -> Constructor
conFromAttr = ?conFromAttr
conForHole :: (NamingScheme) => Sort -> Constructor
conForHole = ?conForHole
conForToken :: (NamingScheme) => Sort -> Constructor
conForToken = ?conForToken
conForSubsortProd :: (NamingScheme) => Sort -> Sort -> Constructor
conForSubsortProd = ?conForSubsortProd
conInjFun :: (NamingScheme) => Sort -> Sort -> Constructor
conInjFun = ?conInjFun
conProjFun :: (NamingScheme) => Sort -> Sort -> Constructor
conProjFun = ?conProjFun
conForFreezer :: (NamingScheme) => Constructor
conForFreezer = ?conForFreezer

-- | Make constructor from from a label, stuff
mkConFromLabel :: Label -> Constructor
mkConFromLabel l = Constructor ("(* "++show l++" *) k_label_"++zencode (show l))

-- | Manufacture a constructor from a sort.
-- Applies a prefix and encodes special characters
mkConFromSort :: Sort -> Constructor
mkConFromSort s | isLegalCoqId (show s) = Constructor (show s)
                | otherwise  = Constructor ("k_sort_"++zencode (show s))

-- TODO: have/use hooks on functions too
-- | Make a constructor/type name given a user-provided name.
-- Argument is used exactly.
mkConFromAttr :: String -> Constructor
mkConFromAttr name = Constructor name

withShared :: ((?conFromLabel :: Label -> Constructor
               ,?conFromSort :: Sort -> Constructor
               ,?conFromAttr :: String -> Constructor)
               => a) -> a
withShared x =
  let ?conFromLabel = mkConFromLabel
      ?conFromSort = mkConFromSort
      ?conFromAttr = mkConFromAttr
  in x


newtype ExplicitNamingScheme = ExplicitNamingScheme {withNamingScheme :: forall a . ((NamingScheme) => a) -> a}

-- make a string for part of a constructor, escaping odd characters
zsort :: Sort -> String
zsort s = zencode (show s)

simpleScheme = ExplicitNamingScheme withSimpleScheme
withSimpleScheme :: ((NamingScheme) => a) -> a
withSimpleScheme x =
  let simpleSubsortProd :: Sort -> Sort -> Constructor
      simpleSubsortProd "KItem" sub = Constructor ('K':zsort sub)
      simpleSubsortProd super sub = Constructor (zsort super++zsort sub)
      simpleInjFun :: Sort -> Sort -> Constructor
      simpleInjFun from "KItem" = Constructor (zsort from++"ToK")
      simpleInjFun from to = Constructor (zsort from++"To"++zsort to)
      simpleProjFun :: Sort -> Sort -> Constructor
      simpleProjFun from "KItem" = Constructor (zsort from++"FromK")
      simpleProjFun from to = Constructor (zsort from++"From"++zsort to)
  in let ?conForHole = \sort -> Constructor ("HOLE_"++zsort sort)
         ?conForToken = \sort -> Constructor (zsort sort++"Token")
         ?conForSubsortProd = simpleSubsortProd
         ?conInjFun = simpleInjFun
         ?conProjFun = simpleProjFun
         ?conForFreezer = Constructor "KFreeze"
  in withShared x

prefixScheme :: ExplicitNamingScheme
prefixScheme = ExplicitNamingScheme withPrefixScheme
withPrefixScheme :: ((NamingScheme) => a) -> a
withPrefixScheme x =
  let prefixSubsortProd :: Sort -> Sort -> Constructor
      prefixSubsortProd super sub = Constructor ("k_wrap_"++zsort sub++"_"++ zsort super)
      prefixInjFun :: Sort -> Sort -> Constructor
      prefixInjFun from to = Constructor ("k_inj_"++zsort from++"_"++zsort to)
      prefixProjFun :: Sort -> Sort -> Constructor
      prefixProjFun from to = Constructor ("k_proj_"++zsort from++"_"++zsort to)
  in let ?conForHole = \sort -> Constructor ("k_HOLE_"++zsort sort)
         ?conForToken = \sort -> Constructor ("k_token_"++zsort sort)
         ?conForSubsortProd = prefixSubsortProd
         ?conInjFun = prefixInjFun
         ?conProjFun = prefixProjFun
         ?conForFreezer = Constructor "k_freeze"
  in withShared x

{- | Check if a string is a legal Coq identifier,
-- enforcing Coq reserved words and our own "k_"
-- namespace in addition to a lexical check.
-}
-- Reserve the k_ prefix for our own use
isLegalCoqId ('k':'_':_) = False
-- avoid reserved words of Coq
isLegalCoqId l | l `elem` reserved = False
 where reserved = ["Variable","Set","Prop","Type"]
-- otherwise, just check the lexical structure
isLegalCoqId (c:s) = isAlpha c && all identChar s
  where identChar c = isAlphaNum c || c == '_'
isLegalCoqId _ = False

data CoqTermVar var = ConApp Constructor [CoqTermVar var]
                    | Lam var (CoqTermVar var)
                    | CoqVar var
                    | CoqList [CoqTermVar var]
  deriving (Typeable,Data,Functor,Foldable)
type CoqTerm = CoqTermVar VarId
type CoqTermOut = CoqTermVar OutVar

coqTermVars :: Traversal (CoqTermVar var) (CoqTermVar var') var var'
coqTermVars f (ConApp c ts) = ConApp c <$> traverse (coqTermVars f) ts
coqTermVars f (Lam v t) = Lam <$> f v <*> coqTermVars f t
coqTermVars f (CoqVar v) = CoqVar <$> f v
coqTermVars f (CoqList ts) = CoqList <$> traverse (coqTermVars f) ts

instance (Show var) => Show (CoqTermVar var) where
  showsPrec p (ConApp (Constructor "MapItem") [l,r]) =
    showParen (p > 5)
      (showsPrec 6 l . (" |-> "++) . showsPrec 6 r)
  showsPrec p (ConApp (Constructor "MapUnion") [l,r]) =
    showParen (p > 4)
      (showsPrec 5 l . (" :* "++) . showsPrec 4 r)
  showsPrec _ (ConApp c []) = shows c
  showsPrec p (ConApp c ts) =
    showParen (p >= 10)
     (shows c . foldr (.) id (map (\t -> (' ':) . showsPrec 10 t) ts))
  showsPrec p (Lam v ts) =
    showParen (p > 0)
     (("fun "++) . shows v . (" => "++) . shows ts)
  showsPrec _ (CoqVar v) = shows v
  showsPrec _ (CoqList ts) =
    ('[':) . foldr (.) id (intersperse ("; "++) (map (showsPrec 0) ts)) . (']':)

flattenVars :: Set VarId -> Map VarId OutVar
flattenVars vs =
  let user = [u | UserVar u <- Set.toList vs]
      gen = [v | v@(GenVar _) <- Set.toList vs]
  in Map.fromList
        ([(UserVar u,OutVar u) | u <- user]
         ++zip gen (map OutVar (map (('x':).show) [(1::Int)..] \\
                    [u | u@('x':t) <- user, all isDigit t])))

publishVars :: LensLike (TwoStage (Set VarId) (Map VarId OutVar)) s t VarId OutVar -> s -> t
publishVars vars = solve vars %~ flattenVars

-- need to clean up vars, print as actual Coq syntax

-- | Describes the Coq implementation of a subtyping relationship,
-- explaining how to inject and extract a term of the subtype from the
-- supertype
data Injection =
   InjConstructor Constructor
   -- ^ A simple wrapping by the given constructor.
 | InjFunctions Constructor
                Constructor
                (Maybe Constructor)
   -- ^ A more complicated injection that must be implemented by functions,
   -- e.g. because the subtypes has subtypes of its own which have direct
   -- wrappings into the supertype.
   -- The first argument is an injection function of type @[| subtype |] -> [| supertype |]@.
   -- The second argument is a projection function of type @[| supertype |] -> option [| subtype |]@.
   -- The final argument, if present, is the constructor of the supertype which
   -- has type @[| subtype |] -> [| supertype |]@ and wraps values of the subtype.
   -- This should only be used when injecting a term that is exactly of the subtype
   -- (e.g, not a variable or a function result, nothing that could possible be an
   -- injection of a value of a yet smaller type),
   -- or when generating the translation functions.

 deriving (Eq,Ord,Show)

data ConvInfo = ConvInfo
  {_convLabels :: Map Label (Constructor, [Sort])
  ,_convHoles :: Map Sort Constructor
  ,_convFreezer :: Constructor
  ,_convInjections :: Map (Sort,Sort) [Injection]
  ,_convTrueTerm :: Term
  }
makeLenses ''ConvInfo

newtype ConvM a = ConvM {unConvM :: RWS ConvInfo [CoqTerm] Int a}
  deriving (Functor,Applicative,Monad)
{- MonadWriter [(VarId,CoqTerm)]
   ,MonadFix) -}
runConvM :: ConvM a -> ConvInfo -> (a,[CoqTerm])
runConvM (ConvM body) info =
  let (a,_,written) = runRWS body info 0
  in (a,written)

constraint :: (VarId -> ConvM CoqTerm) -> ConvM CoqTerm
constraint mkCon = do
  v <- newVar
  _ <- ConvM (mfix (\t -> tell [t] >> unConvM (mkCon v)))
  return (CoqVar v)

newVar :: ConvM VarId
newVar = GenVar <$> ConvM (id <+= 1)

labelCon :: Label -> ConvM (Constructor, [Sort])
labelCon l = do
  table <- ConvM (view convLabels)
  case Map.lookup l table of
    Just con -> return con
    Nothing -> error $ "No Coq constructor registered for label "++show l

freezer :: ConvM Constructor
freezer = ConvM (view convFreezer)

freezerHole :: Sort -> ConvM Constructor
freezerHole s = do
  table <- ConvM (view convHoles)
  case Map.lookup s table of
    Just con -> return con
    Nothing -> error $ "No Coq freezer for sort "++show s

injection :: Sort -> Sort -> ConvM (CoqTerm -> CoqTerm)
injection to from
  | from == to = return id
  | otherwise = do
    table <- ConvM (view convInjections)
    case Map.lookup (from,to) table of
      Nothing -> return (\inner ->
         error $ "No injection found from "++show from++" to "++show to
               ++" when wrapping "++show inner)
      Just path -> return (inject path)

inject :: [Injection] -> CoqTerm -> CoqTerm
inject path t = foldl (flip inject1) t path

inject1 :: Injection -> CoqTerm -> CoqTerm
inject1 (InjConstructor c) t = ConApp c [t]
inject1 (InjFunctions inj _proj _con) t = ConApp inj [t]

injectRigid :: [Injection] -> CoqTerm -> CoqTerm
injectRigid path t = foldl (flip inject1Rigid) t path

-- | Inject a term, using the constructor if it exists even for function-mediated injections.
inject1Rigid :: Injection -> CoqTerm -> CoqTerm
inject1Rigid (InjConstructor c) t = ConApp c [t]
inject1Rigid (InjFunctions inj _ mbCon) t =
    ConApp (fromMaybe inj mbCon) [t]


-- | projection generates logical hypotheses when extraction functions
-- need to be used, so it's not available outside ConvM
projection :: Sort -> Sort -> ConvM (ConvM CoqTerm -> ConvM CoqTerm)
projection to from
  | from == to = return id
  | otherwise = do
    table <- ConvM (view convInjections)
    case Map.lookup (from,to) table of
      Nothing -> return (\minner -> do
                            inner <- minner
                            error $ "No injection found from "++show from++" to "++show to
                              ++" when projecting "++show inner)
      Just path -> return (project path)

project :: [Injection] -> ConvM CoqTerm -> ConvM CoqTerm
project path t = foldl (flip project1) t path

project1 :: Injection -> ConvM CoqTerm -> ConvM CoqTerm
project1 (InjConstructor c) mt = do t <- mt; return (ConApp c [t])
project1 (InjFunctions _inj proj _con) mt = constraint $ \v -> do
  t <- mt
  return (ConApp "eq" [ConApp proj [CoqVar v], ConApp "Some" [t]])

convPattern :: Sort -> Term -> ConvM CoqTerm
convPattern "K" t = case t of
  KSequence _ -> convPattern' t
  Var "K" _ -> convPattern' t
  _ -> convPattern' (KSequence [t])
convPattern tgtSort t = do
  proj <- projection tgtSort (termSort t)
  proj (convPattern' t)

convPattern' :: Term -> ConvM CoqTerm
convPattern' (KApp _ (LCon l) (KList ts)) = do
  (c, sorts) <- labelCon l
  ConApp c <$> zipWithM convPattern sorts ts
convPattern' (KSequence ts) = convKSequence (convPattern (Sort "KItem")) ts
convPattern' (Var _ v) = return (CoqVar (UserVar v))
convPattern' t@(MapUnion _) = convMapPat t
convPattern' t@(MapItem _ _) = convMapPat t
convPattern' (Freezer _ t) = do
  t' <- convPattern "KItem" t
  f <- freezer
  return (ConApp f [t'])
convPattern' (Hole s) = do
  c <- freezerHole s
  return (ConApp c [])
convPattern' (Token (Sort "Int") v) = return (ConApp (Constructor v) [])
convPattern' (Token (Sort "#Int") v) = return (ConApp (Constructor v) [])
convPattern' (BoolToken _ b) = return (ConApp (if b then "true" else "false") [])
convPattern' t = error $ "Internal Errror: Unexpected term in convPattern: "++show t

convKSequence :: (Term -> ConvM CoqTerm) -> [Term] -> ConvM CoqTerm
convKSequence _conv (Var s v:ts)
  | s == Sort "K" =
    case ts of
      [] -> return (CoqVar (UserVar v))
      _ -> fail $ "Can't handle AC matching, K variable "++v++" in middle of KSequence"
convKSequence conv (t:ts) = do
  t' <- conv t
  ts' <- convKSequence conv ts
  return (app2 "kra" t' ts')
convKSequence _conv [] = return (ConApp (Constructor "kdot") [])

app1 ::  Constructor -> CoqTerm -> CoqTerm
app1 con t1 = ConApp con [t1]

app2 ::  Constructor -> CoqTerm -> CoqTerm -> CoqTerm
app2 con t1 t2 = ConApp con [t1,t2]

convMap :: Term -> ConvM CoqTerm
convMap mapTerm = constraint $ \v -> do
  mapPat <- convMapTerm mapTerm
  return (ConApp "MapEquiv" [CoqVar v, mapPat])

convMapPat :: Term -> ConvM CoqTerm
convMapPat mapPat = constraint $ \v -> do
  mapPat <- convMapPattern mapPat
  return (ConApp "MapEquiv" [CoqVar v, mapPat])

-- map builders
mapItem :: CoqTerm -> CoqTerm -> CoqTerm
mapItem = app2 "MapItem"
mapEmpty :: CoqTerm
mapEmpty = ConApp (Constructor "MapEmpty") []
mapUnions :: [CoqTerm] -> CoqTerm
mapUnions [] = ConApp (Constructor "MapEmpty") []
mapUnions ms = foldr1 (app2 "MapUnion") ms

convMapPattern :: Term -> ConvM CoqTerm
convMapPattern (MapUnion ts) = do
  let isItem (MapItem _ _) = True
      isItem _ = False
      (items,rest) = partition isItem ts
  items' <- mapM convMapPattern items
  rest' <- mapM (convPattern (Sort "Map")) rest
  return (mapUnions (items'++rest'))
convMapPattern (MapItem k v) =
  mapItem <$> convPattern (Sort "K") k
          <*> convPattern (Sort "K") v
convMapPattern p = error $ "not a map term: "++show p

convMapTerm :: Term -> ConvM CoqTerm
convMapTerm (MapUnion ts) = do
  let isItem (MapItem _ _) = True
      isItem _ = False
      (items,rest) = partition isItem ts
  items' <- mapM convMapTerm items
  rest' <- mapM (convPattern (Sort "Map")) rest
  return (mapUnions (items'++rest'))
convMapTerm (MapItem k v) =
  mapItem <$> convPattern (Sort "K") k
          <*> convPattern (Sort "K") v
convMapTerm p = error $ "not a map term: "++show p

convTerm :: Sort -> Term -> ConvM CoqTerm
convTerm "K" t = case t of
  KSequence _ -> convTerm' t
  (Var "K" _) -> convTerm' t
  _ -> convTerm' (KSequence [t])
convTerm tgtSort t = injection tgtSort (termSort t) <*> convTerm' t

convTerm' :: Term -> ConvM CoqTerm
convTerm' (KApp _ (LCon l) (KList ts)) = do
  (c, sorts) <- labelCon l
  ConApp c <$> zipWithM convTerm sorts ts
convTerm' (Var _ v) = return (CoqVar (UserVar v))
convTerm' (MapItem k v) = mapItem <$> convTerm (Sort "K") k
                                  <*> convTerm (Sort "K") v
convTerm' (MapUnion ts) = mapUnions <$> mapM (convTerm (Sort "Map")) ts
convTerm' (KSequence ts) = convKSequence (convTerm (Sort "KItem")) ts
convTerm' (Freezer _ t) = do
  t' <- convTerm "KItem" t
  f <- freezer
  return (ConApp f [t'])
convTerm' (Hole s) = do
  c <- freezerHole s
  return (ConApp c [])
convTerm' (Token (Sort "Int") v) = return (ConApp (Constructor v) [])
convTerm' (Token (Sort "#Int") v) = return (ConApp (Constructor v) [])
convTerm' (BoolToken _ b) = return (ConApp (if b then "true" else "false") [])
convTerm' t = error $ "Internal Errror: Unexpected term in convTerm: "++show t

type TermOut var = (CoqTermVar var,[CoqTermVar var])
termOutVars :: Traversal (TermOut var) (TermOut var') var var'
termOutVars = beside coqTermVars (traverse . coqTermVars)

convert :: ConvInfo -> Term -> (CoqTermOut,[CoqTermOut])
convert info t =
  publishVars termOutVars (runConvM (convPattern (Sort "K") t) info)

-- has some sort info and some Coq conversion info baked in
type RuleBody = [(Constructor,Sort,RewriteItem Term)]
data RewriteItem t = Change t t | Match t
  deriving (Show,Eq,Functor,Foldable,Traversable)

instance Applicative RewriteItem where
  pure a = Match a
  Match f <*> Match x = Match (f x)
  Match f <*> (Change l r) = Change (f l) (f r)
  Change f g <*> x = Change (f (lhs x)) (g (rhs x))

lhs :: RewriteItem a -> a
lhs (Match x) = x
lhs (Change l _) = l
rhs :: RewriteItem a -> a
rhs (Match x) = x
rhs (Change _ r) = r

convRule :: RuleBody -> ConvM [CoqTerm]
convRule = mapM (\(con,sort,i) -> convertItem con sort i)

convertItem :: Constructor -> Sort -> RewriteItem Term -> ConvM CoqTerm
convertItem cellCon sort (Change l r) = do
  l' <- convPattern sort l
  r' <- convTerm sort r
  return (ConApp cellCon [ConApp "write" [l',r']])
convertItem cellCon sort (Match t) = do
  -- If we had to lift out any maps, we degrade to a modification
  -- to put it back in the order we prefer (TODO: maybe just leave alone?)
  (t',pats) <- ConvM (listen (unConvM (convPattern sort t)))
  if null pats then
    return (ConApp cellCon [ConApp "read" [t']])
  else do
    r' <- convTerm sort t
    return (ConApp cellCon [ConApp "write" [t',r']])

convertRule :: ConvInfo -> Constructor -> Maybe Term -> RuleBody -> String
convertRule info relName sideCondition rule =
  let ((t,cond,trueConst),preconditions) = flip runConvM info $ do
        tm <- convRule rule
        sideCondition <- traverse (convTerm (Sort "Bool")) sideCondition
        trueConst <- convTerm (Sort "Bool") (info ^. convTrueTerm)
        return (tm, sideCondition, trueConst)
      names = flattenVars $ Set.fromList (concatMap toList t++concatMap toList preconditions
                            ++ foldMap toList cond
                            ++ toList trueConst)
      fixVar = (Map.!) names
      fixVars = fmap fixVar
      prefix = if Map.null names then "" else
                 "forall "++unwords (map show (Map.elems names))++", "
  in prefix++
     foldr (\k r -> k++" -> "++r)
      (case cond of
          Nothing -> ""
          Just cond' -> show (ConApp "eq" [fixVars cond', fixVars trueConst])
                        ++" -> "
       ++ show (ConApp "krule" [ConApp relName [], CoqList (map fixVars t)]))
        (map (show . fixVars) preconditions)
