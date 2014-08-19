{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Attributes where
import Data.Data
import Data.Maybe(listToMaybe)
import Data.List(intercalate)

import Control.Lens

-- | A K attribute. Missing and empty arguments are not distinguished, arguments are not parsed.
data Attribute = Attribute String String
  deriving (Eq,Ord,Typeable,Data)
instance Show Attribute where
  show (Attribute label "") = label
  show (Attribute label body) = label++"("++body++")"

-- | An attribute list
type Attributes = [Attribute]

-- | Show a list of attributes in K syntax
showAttrs :: Attributes -> String
showAttrs [] = ""
showAttrs attrs = " ["++intercalate ", " (map show attrs)++"]"

-- | A type class for things having attributes
class HasAttributes a where
  -- | A 'Lens' to the attributes.
  attributes :: Lens' a Attributes
instance HasAttributes Attributes where
  attributes = id

-- | Get the value of the requested attribute, the first if there are several.
getAttr :: (HasAttributes t) => String -> t -> Maybe String
getAttr k t = listToMaybe [v | Attribute k' v <- t ^. attributes, k' == k]

-- | Get all values of attributes with the given key.
getAttrs :: (HasAttributes t) => String -> t -> [String]
getAttrs key t = [v | Attribute k' v <- t ^. attributes, k' == key]

-- | True if any attribue with the given key exists.
hasAttr :: (HasAttributes t) => String -> t -> Bool
hasAttr k t = any (\(Attribute k' _) -> k' == k) (t ^. attributes)
