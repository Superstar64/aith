module Main where

import C.Print
import Codegen
import Core.Ast.Common
import Core.TypeCheck
import Misc.Silent
import Misc.Syntax
import Module hiding (modulex)
import Syntax
import System.Exit
import Text.Megaparsec hiding (parse)

tryParse p = do
  case p of
    Right x -> pure x
    Left error -> do
      putStrLn (errorBundlePretty error)
      exitWith (ExitFailure 1)

termMain :: IO ()
termMain = do
  stdin <- getContents
  e' <- tryParse $ parse (withSourcePos term) "stdin" stdin
  let e = (: []) <$> e'
  σ <- runCore (typeCheck @[SourcePos] e) $ emptyState
  κ <- runCore (typeCheck @Internal σ) $ emptyState
  putStrLn "Term Pretty: " >> prettyPrint term (Internal <$ e)
  putStrLn ""
  putStrLn "Term β Pretty: " >> prettyPrint term (reduce $ Internal <$ e)
  putStrLn ""
  putStrLn "Type Pretty: " >> prettyPrint typex σ
  putStrLn ""
  putStrLn "Kind Pretty: " >> prettyPrint kind κ

readModule :: String -> IO (Module Silent Internal)
readModule path = do
  file <- readFile path
  code <- tryParse $ parse (withInternal modulex) path file
  pure code

moduleMain :: IO ()
moduleMain = do
  stdin <- getContents
  code' <- tryParse $ parse (withSourcePos modulex) "stdin" stdin
  let code = (: []) <$> code'
  putStrLn "Module Pretty: " >> prettyPrint modulex (Internal <$ code)
  ordering <- order code
  typeCheckModule ordering
  let code' = unorder $ reduceModule $ (Internal <$ ordering)
  putStrLn "Module β Pretty: " >> prettyPrint modulex code'
  putStrLn "C: " >> prettyPrint globals (compileModule [] code')
  pure ()

codegenMain :: IO ()
codegenMain = do
  stdin <- getContents
  code' <- tryParse $ parse (withSourcePos modulex) "stdin" stdin
  let code = (: []) <$> code'
  ordering <- order code
  typeCheckModule ordering
  let code' = unorder $ reduceModule $ (Internal <$ ordering)
  prettyPrint globals (compileModule [] code')
  pure ()

main = moduleMain
