{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-|
Description: Parse a complete definition, chasing requires and checking
that requires and module imports are valid.
-}
module RequireChaser(parseFile) where
import           Prelude hiding(mapM)
import           Control.Applicative((<$>))
import           Control.Monad(forM_,mzero,unless)
import           Control.Monad.Trans(liftIO)
import           Control.Monad.Trans.Maybe(MaybeT(MaybeT),runMaybeT)
import           Control.Exception(evaluate)
import           Control.Concurrent(forkIO,getNumCapabilities)
import           Control.Concurrent.Async(Concurrently(Concurrently),runConcurrently)
import           Control.Concurrent.STM(atomically,TVar,newTVarIO,readTVar,writeTVar,
                                        TMVar,newEmptyTMVar,putTMVar,readTMVar)
import           Control.Concurrent.QSem(newQSem,waitQSem,signalQSem)

import           Data.List(isPrefixOf)
import           Data.Maybe(catMaybes,fromJust)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Foldable(traverse_)
import           Data.Traversable(mapM)

import           System.FilePath(takeDirectory, (</>))
--import           System.FilePath(takeBaseName)
import           System.Directory(doesFileExist, canonicalizePath)
import           System.Environment (getExecutablePath)
import           Text.Parsec (ParseError)

-- tracing stuff
import           Control.Concurrent(myThreadId)
import           Debug.Trace(traceEventIO)
import           GHC.Conc(labelThread)

import           BasicParser
import           Definition
import           GraphTools
import           Module

{- |
   An STM-based cache, mapping 'k' to 'v'

   The first thread to request an entry is responsible for
   filling it, and later threads will block until a value is
   available.
 -}
newtype Cache k v = Cache (TVar (Map k (TMVar v)))

-- | Create a new empty cache
newCache :: IO (Cache k v)
newCache = Cache <$> newTVarIO Map.empty

-- | Peek at the current cache contexts as a 'Map'
readCache :: Cache k v -> IO (Map k v)
readCache (Cache c) = atomically (readTVar c >>= mapM readTMVar)

{- |
  Look up the cached value.
  Returns 'Right' of a value if it was found in the cache,
  otherwise the current thread becomes responsible for filling it,
  and receives 'Left' of a callback that must be called once
  on the value to fill the entry with.

  A call will block for an extended period of time only if
  it's not the first to request an entry, but the entry
  hasn't been filled yet.

  Calling the callback more than once will block indefinitely.
 -}
-- TODO: compare to async's exception handling
cacheLookup :: Ord k => Cache k v -> k -> IO (Either (v -> IO ()) v)
cacheLookup (Cache c) key = do
  found <- atomically $ do
    table <- readTVar c
    case Map.lookup key table of
      Just vvar -> return (Right vvar)
      Nothing -> do
        vvar <- newEmptyTMVar
        writeTVar c (Map.insert key vvar table)
        return (Left vvar)
  case found of
    Right cached -> do
      val <- atomically (readTMVar cached)
      return (Right val)
    Left inserted -> do
      return (Left (\val -> atomically (putTMVar inserted val)))

{- | Call the function on values in the list until a 'Just' is
   returned, or the end is reached.
 -}
mapFirstMaybeM :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
mapFirstMaybeM _ [] = return Nothing
mapFirstMaybeM f (a:as) = do
  r <- f a
  case r of
    Just _ -> return r
    Nothing -> mapFirstMaybeM f as

-- | Where to try looking for a require
searchPath :: FilePath -- ^ The include directory
           -> FilePath -- ^ The file containing the require
           -> FilePath -- ^ The path required
           -> [FilePath]
searchPath includeDirectory basePath target =
  [takeDirectory basePath </> target
  ,includeDirectory </> target
  ]

-- | Returns the first file satisfying a require, if there is any.
resolvePath :: FilePath -- ^ The include directory
            -> FilePath -- ^ The file containing the require
            -> FilePath -- ^ The path required
            -> IO (Maybe FilePath)
resolvePath includePath basePath target =
  flip mapFirstMaybeM (searchPath includePath basePath target) $ \entry -> do
    exists <- doesFileExist entry
    if exists then Just <$> canonicalizePath entry else return Nothing


{- | Parse a single K file.
   Returns after parsing up to and resolving the requires
   (which must come before any other non-comment items),
   the inner 'Either' will report parse errors that occur
   after the requires are extracted.
 -}
parseOne :: FilePath -> FilePath
         -> IO (Either ParseError
                (Map FilePath (Maybe FilePath),
                 Either ParseError Definition))
parseOne includeDirectory definition = do
  result <- splitParseFile definition
  case result of
    Left err -> return (Left err)
    Right (reqs, bodyParse) -> do
      let requires =
            if includeDirectory `isPrefixOf` definition
            then reqs else (includeDirectory </> "autoinclude.k"):reqs
      includes <- mapM (resolvePath includeDirectory definition) requires
      return (Right (Map.fromList (zip requires includes),bodyParse))

{- | Parse the given files, and anything transitively required.
   The result is a 'Map' with an entry for each reached file.
   If parsing was successful, the value is a 'Definition' paired with
   a 'Map' from the names required to the full paths they were resolved to,
   if the required file was found at all.
-}
parseDefinition :: FilePath -- ^ The include directory
                -> [FilePath] -- ^ The roots to parse from
                -> IO (Map FilePath (Either ParseError
                                     (Definition, Map FilePath (Maybe FilePath))))
parseDefinition includeDirectory roots = do
  cache <- newCache :: IO (Cache FilePath (Either ParseError
                                      (Definition, Map FilePath (Maybe FilePath))))
  sem <- getNumCapabilities >>= newQSem
  let visit definition = do
        do tid <- myThreadId; labelThread tid definition
        cached <- cacheLookup cache definition
        case cached of
          Right _ -> return () -- already visited
          Left callback -> do
            waitQSem sem
            traceEventIO $ "START parse "++definition
            parse <- parseOne includeDirectory definition
            case parse of
              Left err -> callback (Left err) >> signalQSem sem
              Right (required, defParsing) -> do
                let result = case defParsing of
                      Left err -> Left err
                      Right def -> Right (def,required)
                callback result
                _ <- forkIO $ do
                     _ <- evaluate result
                     signalQSem sem
                     traceEventIO ("STOP parse "++definition)
                let found = catMaybes (Map.elems required)
                runConcurrently $ traverse_ (Concurrently . visit) found
  mapM_ (\p -> canonicalizePath p >>= visit) roots
  readCache cache

-- Now starting analysis

{- | Given a table of file parses as produced by 'parseDefinition',
   check that all parses were actually successful, and all required files were found.
   Prints error messages if there were problems, otherwise removes those
   possibilities from the type.
 -}
checkDefinition :: (Map FilePath (Either ParseError
                                      (Definition, Map FilePath (Maybe FilePath))))
                   -> IO (Maybe (Map FilePath (Definition, Map FilePath FilePath)))
checkDefinition defs = runMaybeT $ do
  let errs = [e | Left e <- Map.elems defs]
  unless (null errs) $ do
    liftIO $ putStrLn "Parse Errors:"
    liftIO $ mapM_ print errs
    mzero
  let missing = [(base,inc) | (base, Right (_, includes)) <- Map.toList defs
                            , (inc,Nothing) <- Map.toList includes]
  unless (null missing) $ do
    liftIO $ putStrLn "Required files not found:"
    liftIO $ forM_ missing $ \(base,inc) -> do
      putStrLn $ "Could not resolve include "++show inc++" from file "++show base
    mzero
  return (Map.map (\(Right (def, includes)) -> (def, Map.map fromJust includes)) defs)

{- | Table of hardcoded/Maude builtin modules.
   Imports of these are fine even though no K file defines them.
 -}
builtinModules :: Set ModuleName
builtinModules = Set.fromList (map ModuleName
  ["#BOOL-INTERFACE"
  ,"#INT-INTERFACE"
  ,"#K-EQUAL-INTERFACE"
  ,"#COUNTER-INTERFACE"
  ,"#FLOAT-INTERFACE"
  ,"#STRING-INTERFACE"
  ,"#TCP-INTERFACE"
  ,"#RANDOM-INTERFACE"
  ,"#K-PARSER-INTERFACE"
  ,"#K-PRINTER-INTERFACE" 
  ,"#SMT" 
  ])

{- | Extract a list of modules and their imports from a 'Definition'.
   Uses the path of the definition and the include directory to
   add "AUTO-INCLUDED-MODULE" unless the definition came from
   the include directory
 -}
modulesWithImports :: FilePath -> FilePath -> Definition -> [(Module,[ModuleName])]
modulesWithImports includeDirectory defPath (Definition items) =
  let standardLibrary = includeDirectory `isPrefixOf` defPath
  in [(m, (if standardLibrary then id else (ModuleName "AUTO-INCLUDED-MODULE":))
          (moduleImports m))
      | ModuleItem m <- items]

{- |
  Given a table of successfully parsed files with successfully resolved
  requires, as returned by 'checkDefinition',
  check that all module imports refer to modules that exist and
  are visible respecting requires.
  Prints errors and returns 'Nothing' if not,
  otherwise returns a table of modules indexed by name, paired with
  a list of the imported modules - the explicit imports, plus
  "AUTO-INCLUDED-MODULE" if appropriate.
 -}
checkIncludes :: FilePath
              -> Map FilePath (Definition, Map FilePath FilePath)
              -> IO (Maybe (Map ModuleName (Module,[ModuleName])))
checkIncludes includeDirectory defs = runMaybeT $ do
  let moduleLocs = Map.fromListWith (++)
         [(modName, [def]) | (def, (Definition items, _)) <- Map.toList defs,
                              (ModuleItem (Module modName _)) <- items]
      repeated = Map.toList (Map.filter ((>1).length) moduleLocs)
      moduleLoc = Map.map head moduleLocs
  unless (null repeated) $ do
    liftIO $ putStrLn "Repeated modules:"
    liftIO $ forM_ repeated $ \(name,paths) ->
      putStrLn $ "Module "++show name++" defined in each of "++unwords (map show paths)
    mzero
  -- now we know they are not repeated, so we can just represent modules by name
  -- compute strongly connected components in the requires graph, accumulate the visible
  -- modules, check that all the includes are visible
  let visibility = topoSweep' visibleAfterGroup 
         [(def,file,Map.elems incs) | (file,(def,incs)) <- Map.toList defs]
      visibleAfterGroup groupNodes visibleImports =
        Set.unions [Set.unions (Map.elems visibleImports)
                   ,Set.fromList [modName | Definition items <- groupNodes,
                                  ModuleItem (Module modName _) <- items]
                   ,builtinModules 
                   ]
      badIncludes = [(file,parentMod,target) |
                       (file,(def,_)) <- Map.toList defs,
                       let visible = visibility Map.! file,
                       ((Module parentMod _),targets) <- modulesWithImports includeDirectory file def,
                       target <- targets,
                       not (Set.member target visible)
                       ]
  unless (null badIncludes) $ do
    liftIO $ forM_ badIncludes $ \(file,parentMod,target) -> do
      putStrLn $ "Invalid include: "++show target++" not visible from module "
        ++show parentMod++" in file "++show file
      case Map.lookup target moduleLoc of
        Nothing -> return ()
        Just rfile -> putStrLn $ "  (maybe require file "++show rfile++")"
    mzero
  return (Map.fromList [(modName,modInfo)
                       | (file,(def,_)) <- Map.toList defs,
                         modInfo@(Module modName _, _) <-
                           modulesWithImports includeDirectory file def
                       ])

{- | Parse a definition beginning from the given file -}
parseFile :: FilePath -> FilePath -> IO (Maybe (Map ModuleName (Module,[ModuleName])))
parseFile includeDirectory mainFile = runMaybeT $ do
  definitions <- MaybeT (checkDefinition =<< parseDefinition includeDirectory [mainFile])
  MaybeT (checkIncludes includeDirectory definitions)
