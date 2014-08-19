{-# LANGUAGE DeriveFunctor, RankNTypes, ConstraintKinds, FlexibleContexts, ImplicitParams #-}
module Main where
import qualified Data.Map as Map
import System.IO
import System.Environment(getExecutablePath)
import System.FilePath(takeDirectory,(</>))

import Options.Applicative
import Data.Data.Lens(template)
import Control.Lens ((^..))

import Module(Module)
import Definition(Definition(Definition),DefinitionItem(ModuleItem))

import CoqConversion(NamingScheme,ExplicitNamingScheme,withNamingScheme,simpleScheme,prefixScheme)

import RuleConversion(translateRules')
import TypeAnalysis(analyze)
import TypeConversion(translateSyntax)
import BasicParser(basicParseFile)
import RequireChaser(parseFile)
import Module(_RuleItem)
import Grammar(Sort,Label,LabelScheme,noQuoteLabel,defaultLabel)

data CommonOptions = CommonOptions
  {namingScheme :: ExplicitNamingScheme
  ,labelScheme :: [Either String Sort] -> Maybe Label
  }
commonOpts :: Parser CommonOptions
commonOpts = CommonOptions
  <$> flag prefixScheme simpleScheme
    (long "simple-names" <> help "use unprefixed naming scheme, which avoids fewer conflicts")
  <*> flag defaultLabel noQuoteLabel
    (long "no-quotes" <> help "make default labels without leading quote")

withCommonOptions :: CommonOptions -> ((NamingScheme, LabelScheme) => a) -> a
withCommonOptions common a =
  let ?defaultLabel = labelScheme common in
  withNamingScheme (namingScheme common) a

data RuleOptions = RuleOptions
  {ruleInputFile :: FilePath
  ,ruleOutputFile :: Maybe FilePath
  ,extraRules :: Maybe FilePath
  ,rulesFrom :: Maybe FilePath
  ,langName :: String
  ,ruleShared :: SharedOptions
  }
data SyntaxOptions = SyntaxOptions
  {syntaxInputFile :: FilePath
  ,syntaxOutputFile :: Maybe FilePath
  ,syntaxShared :: SharedOptions
  }

data ParseRecursive = ProcessRequires | SkipRequires
  deriving (Eq,Ord,Show)

data SharedOptions = SharedOptions
  {recursiveParse :: ParseRecursive
  ,includeDir :: Maybe FilePath}

sharedOpts :: Parser SharedOptions
sharedOpts = SharedOptions
  <$> flag SkipRequires ProcessRequires  (long "recursive" <> help "process requires")
  <*> optional (fileOption "include-dir"
                  (metavar "PATH" <> help "look for required files also under this directory"))

fileOption :: String -> Mod OptionFields FilePath -> Parser FilePath
fileOption longFlag opts = strOption (long longFlag <> metavar "FILE" <> action "file" <> opts)

fileArgument :: Mod ArgumentFields FilePath -> Parser FilePath
fileArgument opts = argument str (metavar "FILE" <> action "file" <> opts)

ruleOpts :: ParserInfo RuleOptions
ruleOpts = info (RuleOptions
  <$> fileArgument idm
  <*> optional (fileArgument (metavar "TARGET" <> help "Output to this file, default stdout"))
  <*> optional (fileOption "extra-rules"
            (help "include this file into generated relation definition"))
  <*> optional (fileOption "rules-from"
            (help "Read labeled rules from this file instead of main input file"))
  <*> (strOption (long "lang-name" <> help "base name for Coq modules")
       <|> pure "fun")
  <*> sharedOpts)
    (progDesc "Generate Coq transition relation from K definition" <> briefDesc)

syntaxOpts :: ParserInfo SyntaxOptions
syntaxOpts = info (SyntaxOptions
  <$> fileArgument idm
  <*> optional (fileArgument (metavar "TARGET" <> help "Output to this file, default stdout"))
  <*> sharedOpts)
    (progDesc "Generate Coq data types from K definition" <> briefDesc)

type LabelOptions = (FilePath, SharedOptions)
labelOpts :: ParserInfo LabelOptions
labelOpts = info ((,) <$> fileArgument idm <*> sharedOpts)
   (progDesc "Check for repated labels in K definition")

opts :: ParserInfo (CommonOptions, Either RuleOptions SyntaxOptions)
opts = info ((,)
  <$> commonOpts
  <*> hsubparser (
       command "rules" (Left <$> ruleOpts)
    <> command "syntax" (Right <$> syntaxOpts)
    <> metavar "[rules|syntax] OPTIONS")
  <**> helper)
    (progDesc "Translate K definition to Coq" <> fullDesc)

main :: IO ()
main = customExecParser (prefs noBacktrack) opts >>= \(common,opts) ->
  withCommonOptions common (either ruleMain syntaxMain opts)

-- TODO: have some idea of a main module, and compute reachability from it
getDefinitionModules :: SharedOptions -> FilePath -> IO [Module]
getDefinitionModules opts inputFile = case recursiveParse opts of
  SkipRequires -> do
    result <- basicParseFile inputFile
    case result of
      Left err -> fail (show err)
      Right (Definition ditems) ->
        let mods = [m | ModuleItem m <- ditems]
        in return mods
  ProcessRequires -> do
    includeDirectory <- case includeDir opts of
      Just path -> return path
      Nothing -> fmap (\prog -> takeDirectory prog </> "../../../include") getExecutablePath
    result <- parseFile includeDirectory inputFile
    case result of
      Nothing -> fail "Parse Error"
      Just moduleMap ->
        let mods = map fst (Map.elems moduleMap)
        in return mods

newtype ErrorGatherM a = ErrorGatherM (Either [String] a)
  deriving (Functor)
getErrors (ErrorGatherM m) = either id (const []) m
instance Applicative ErrorGatherM where
  pure x = ErrorGatherM (Right x)
  ErrorGatherM (Right f) <*> ErrorGatherM (Right x) = pure (f x)
  f <*> x = ErrorGatherM (Left (getErrors f++getErrors x))
instance Monad ErrorGatherM where
  return x = pure x
  ErrorGatherM (Left e) >>= _ = ErrorGatherM (Left e)
  ErrorGatherM (Right x) >>= f = f x
  fail err = ErrorGatherM (Left [err])

ruleMain :: (NamingScheme, LabelScheme) => RuleOptions -> IO ()
ruleMain (RuleOptions inputFile outputFile extraRules ruleFile langName sharedOpts) = do
  let write = case outputFile of
        Nothing -> putStr
        Just f -> writeFile f
  extraLines <- case extraRules of
    Nothing -> return []
    Just f -> fmap lines (readFile f)
  mods <- getDefinitionModules sharedOpts inputFile
  rules <- case ruleFile of
    Nothing -> return (mods ^.. template . _RuleItem)
    Just rules -> do
      result <- basicParseFile rules
      case result of
        Left err -> fail (show err)
        Right def -> return (def ^.. template . _RuleItem)
  conversionInfo <- case analyze mods of
    ErrorGatherM (Left errs) -> putStrLn "Errors:" >> mapM_ putStrLn errs >> fail ""
    ErrorGatherM (Right ci) -> return ci
  case translateRules' conversionInfo rules of
    ErrorGatherM (Left errs) -> putStrLn "Errors:" >> mapM_ putStrLn errs
    ErrorGatherM (Right clauses) -> do
      write $ unlines $
        ["Require Import ZArith."
        ,"Require Import String."
        ,""
        ,"Require Export "++langName++"_domains."
        ,"Require Export "++langName++"_domains_aux."
        ,""
        ,"Set Implicit Arguments."
        ,""
        ,"Inductive kstep : kcfg -> kcfg -> Prop :="]
        ++ extraLines
        ++ clauses
        ++ ["."]

syntaxMain :: (NamingScheme, LabelScheme) => SyntaxOptions -> IO ()
syntaxMain (SyntaxOptions inputFile outputFile sharedOpts) = do
  let write = case outputFile of
        Nothing -> putStr
        Just f -> writeFile f
  mods <- getDefinitionModules sharedOpts inputFile
  case translateSyntax mods of
    ErrorGatherM (Left errs) -> putStrLn "Errors:" >> mapM_ putStrLn errs
    ErrorGatherM (Right definitions) -> do
      write $ unlines $
        ["Require Import ZArith."
        ,"Require Import String."
        ,"Require Export maps."
        ,""
        ,"Set Implicit Arguments."
        ,"Inductive float : Set :=."
        ,""]
        ++ definitions
