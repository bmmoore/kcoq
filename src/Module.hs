{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-|
Description: Type for K module
 -}
module Module where
import Data.Data

import Control.Lens

import Grammar

newtype ModuleName = ModuleName String
  deriving (Eq,Ord,Data,Typeable)
instance Show ModuleName where
  show (ModuleName name) = name

data ModuleItem =
     SyntaxItem Syntax
   | PriorityItem Priorities
   | NoFollowItem NoFollow
   | ImportsItem ModuleName
   | RuleItem String
   | ConfigurationItem String
   | ContextItem String
   | ModuleCommentItem String
  deriving (Eq,Data,Typeable)
makePrisms ''ModuleItem
instance Show ModuleItem where
  show (SyntaxItem syn) = show syn++"\n"
  show (PriorityItem priorites) = show priorites++"\n"
  show (NoFollowItem n) = show n++"\n"
  show (ImportsItem modName) = "imports "++show modName++"\n"
  show (RuleItem body) = "rule "++body++"\n"
  show (ConfigurationItem body) = "configuration "++body++"\n"
  show (ContextItem body) = "context "++body++"\n"
  show (ModuleCommentItem comment) = comment++(if last comment /= '\n' then "\n" else "")

data Module = Module {moduleName::ModuleName, moduleItems::[ModuleItem]}
  deriving (Eq,Data,Typeable)

moduleImports :: Module -> [ModuleName]
moduleImports (Module _ items) = [name | ImportsItem name <- items]

instance Show Module where
  show (Module name items) =
    "module "++show name++"\n"
    ++concatMap show items
    ++"endmodule\n"
