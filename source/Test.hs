module Main where

import BaseMain
import Data.List
import System.Directory
import System.Exit
import Prelude hiding (readFile)

execute args = do
  putStrLn $ "aith " ++ intercalate " " args
  baseMain args

diff one two = do
  putStrLn $ "diff " ++ one ++ " " ++ two
  one' <- readFile one
  two' <- readFile two
  if one' /= two'
    then exitFailure
    else pure ()

main :: IO ()
main = do
  createDirectoryIfMissing True "build"
  execute $ "--load" : "test.aith" : "/test" : "--format" : "/test" : "build/test-format.aith" : []
  execute $ "--load" : "build/test-format.aith" : "/test" : "--format" : "/test" : "build/test-format2.aith" : []
  diff "build/test-format.aith" "build/test-format2.aith"

  execute $ "--load" : "test.aith" : "/test" : "--annotate" : "/test" : "build/test-annotate.aith" : []
  execute $ "--load" : "build/test-annotate.aith" : "/test" : "--annotate" : "/test" : "build/test-annotate2.aith" : []
  diff "build/test-annotate.aith" "build/test-annotate2.aith"

  execute $ "--load" : "test.aith" : "/test" : "--reduce" : "/test" : "build/test-reduce.aith" : []
  execute $ "--load" : "build/test-reduce.aith" : "/test" : "--reduce" : "/test" : "build/test-reduce2.aith" : []
  diff "build/test-reduce.aith" "build/test-reduce2.aith"
