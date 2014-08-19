module ParserTest where
import Text.Parsec
import Text.Parsec.String
import Control.Applicative
import BasicParser

-- testing

-- need to find and parse everything, 5_types has irregular names

ktut file = "/home/brandon/code/k/k-framework/tutorial/1_k/" ++ file

readKTut tut file n = ktut $ tut ++"/lesson_"++n++"/"++file
readKTut' tut file n = readKTut tut file (show n)

readLamTut   n = readKTut' "1_lambda"   "lambda.k" n
readImpTut   n = readKTut' "2_imp"      "imp.k" n
readLamppTut n = readKTut' "3_lambda++" "lambda.k" n
readImppp    n = readKTut' "4_imp++"    "imp.k" n

typeFiles =
 ["./5_types/lesson_9/lambda.k"
 ,"./5_types/lesson_7/lambda.k"
 ,"./5_types/lesson_5.5/lambda.k"
 ,"./5_types/lesson_3/lambda.k"
 ,"./5_types/lesson_2/lambda.k"
 ,"./5_types/lesson_1/imp.k"
 ,"./5_types/lesson_8/lambda.k"
 ,"./5_types/lesson_9.5/meta-k.k"
 ,"./5_types/lesson_9.5/lambda.k"
 ,"./5_types/lesson_6/lambda.k"
 ,"./5_types/lesson_1.9/lambda.k"
 ,"./5_types/lesson_4/lambda.k"
 ,"./5_types/lesson_5/lambda.k"
 ]

readTut n = readImppp n
test n = testFile (readTut n)

testFile file = do
  r <- parseFromFile (whiteSpace *> kdefinition <* eof) file
  case r of
    Left err -> putStr "parse error at " >> print err
    Right v -> print v

checkFile file = do
  r <- parseFromFile (whiteSpace *> kdefinition <* eof) file
  case r of
    Left err -> print err
    Right _ -> return ()

kdir = "/home/brandon/code/k/k-framework/"

testAll = mapMUntil_ check =<< fmap (map (kdir++) . lines) (readFile (kdir++"ks"))
 where check f = do
         r <- parseFromFile (whiteSpace *> kdefinition <* eof) f
         case r of
           Left err -> print err >> return False
           Right v ->
             case parse (whiteSpace *> kdefinition <* eof) "<reparsing>" (show v) of
               Left err -> do putStrLn $ "Error while reparsing "++show f
                              print err
                              return False
               Right v' -> if v == v'
                              then return True
                              else do putStrLn $ "reparsing changed "++show f
                                      return False

mapMUntil_ :: (Monad m) => (a -> m Bool) -> [a] -> m ()
mapMUntil_ p (x:xs) = do
  ok <- p x
  if ok then mapMUntil_ p xs else return ()
mapMUntil_ _ [] = return ()
