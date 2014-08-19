{-# LANGUAGE DeriveDataTypeable #-}
{-|
Description: Types for top level of definition
 -}
module Definition where
import Data.Data

import Module

data DefinitionItem =
     RequireItem String
   | DefinitionCommentItem String
   | ModuleItem Module
  deriving (Eq,Data,Typeable)
instance Show DefinitionItem where
  show (RequireItem file) = "require "++show file++"\n"
  show (DefinitionCommentItem comment) = comment++(if last comment /= '\n' then "\n" else "")

  show (ModuleItem kmodule) = show kmodule

data Definition = Definition {definitionItems::[DefinitionItem]}
  deriving (Eq,Data,Typeable)

instance Show Definition where
  show (Definition items) = concatMap show items
