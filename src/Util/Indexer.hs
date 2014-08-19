{- | Building up mappings between sets of values and sequential 'Int' codes. -}
module Util.Indexer where
import qualified Data.IntMap as IntMap
import           Data.IntMap(IntMap)
import qualified Data.Map as Map
import           Data.Map(Map)

-- | An assignment of distinct 'Int' indices to a set of values of type 'a'.
data Indexer a = Indexer !(Map a Int) !(IntMap a) !Int
  deriving (Show)

-- | An empty 'Indexer'.
newIndexer :: Indexer a
newIndexer = Indexer Map.empty IntMap.empty 1

-- | Return an 'Indexer' which covers the given argument, extending it if necessary.
assignIx :: (Ord a) => Indexer a -> a -> Indexer a
assignIx ix v = snd (intern ix v)

-- | Return a code for the given value, extending and returning the 'Indexer' if necessary.
intern :: (Ord a) => Indexer a -> a -> (Int, Indexer a)
intern ix@(Indexer known rev next) v =
  case Map.lookup v known of
    Just i -> (i, ix)
    Nothing -> (next, Indexer (Map.insert v next known) (IntMap.insert next v rev) (next+1))

-- | Return the index for the given argument, if one has been assigned
translate :: (Ord a) => Indexer a -> a -> Maybe Int
translate (Indexer known _ _) v = Map.lookup v known

-- | Retrieve the value corresponding to an index, if it has been assigned.
retrieve :: Indexer a -> Int -> Maybe a
retrieve (Indexer _ rev _) v = IntMap.lookup v rev

