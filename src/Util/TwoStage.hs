{-# LANGUAGE DeriveFunctor #-}
module Util.TwoStage where
import           Control.Applicative
import           Control.Lens
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.Monoid

data TwoStage a b r = TwoStage a (b -> r)
  deriving (Functor)
type TwoStage' m a b = TwoStage m (Map a b)
instance Monoid a => Applicative (TwoStage a b) where
  pure x = TwoStage mempty (const x)
  TwoStage a f <*> TwoStage b g = TwoStage (a <> b) (f <*> g)

runTwoStage :: (Functor f) => (a -> f b) -> TwoStage a b x -> f x
runTwoStage f (TwoStage a k) = fmap k (f a)

solveIx :: (Profunctor p, Ord a, Ord i, Functor f)
        => Optical (Indexed i) p (TwoStage (Endo (Map a  (Set i))) (Map a b)) s t a b
        -> (Map a (Set i) -> f (Map a b)) -> p s (f t)
solveIx problems solver = rmap (runTwoStage (solver . flip appEndo Map.empty))
                               (problems  (Indexed (\i a -> TwoStage (putEntry i a) (Map.! a))))
  where putEntry i a = Endo (Map.insertWith Set.union a (Set.singleton i))

solve :: (Ord a, Functor f)
      => LensLike (TwoStage (Set a) (Map a b)) s t a b
      -> (Set a -> f (Map a b)) -> s -> f t
solve problems solver = rmap (runTwoStage solver)
                             (problems (\a -> TwoStage (Set.singleton a) (Map.! a)))
