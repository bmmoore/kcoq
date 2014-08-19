{-|
Descriptions: Graph utilites, esp. cycle-aware fold
 -}
module GraphTools where
import           Data.List(foldl',nub,(\\))
import qualified Data.Map as Map
import           Data.Map(Map)
import           Data.Monoid
import           Data.Foldable (foldMap,fold)

import           Data.Graph

-- Given nodes with keys and labeled values, perform a fold over the strongly connected
-- components.
-- The supplied function recievies a list of nodes making up a strongly connected
-- component, and a table giving values for all the links leaving the component,
-- and returns a list of result values for each node in the component.
-- The result is the list of the original nodes, annotated with their values.
topoSweep :: Ord k => ([(v,k,[k])] -> Map k a -> [a]) -> [(v,k,[k])] -> Map k a
topoSweep computeGroup = foldl' updateScc Map.empty . stronglyConnCompR
  where updateScc values component =
          let nodes = flattenSCC component
              keys = [k | (_,k,_) <- nodes]
              imports = nub (concat [ks | (_,_,ks) <- nodes]) \\ keys
              info = Map.filterWithKey (\k _ -> k `elem` imports) values
              labels = computeGroup nodes info
          in Map.union values (Map.fromList (zip keys labels))

-- A simplified variant of topoSweep which assumes every node in a connected component
-- will get the same result, and that result doesn't depend on the keys of any of
-- the nodes in the component, or from which node in the component out-edges originate
topoSweep' :: Ord k => ([v] -> Map k a -> a) -> [(v,k,[k])] -> Map k a
topoSweep' simpleFun = topoSweep (\nodes info -> let r = simpleFun [v | (v,_,_) <- nodes] info
                                                 in map (const r) nodes)

-- An especially simple case is when the desired information is
-- just the (commutative) monoidal sum of summaries that can be produced locally
monoidSweep :: (Monoid r, Ord k) => (v -> r) -> [(v,k,[k])] -> Map k r
monoidSweep localValue = topoSweep' (\vs incoming -> foldMap localValue vs <> fold incoming)
