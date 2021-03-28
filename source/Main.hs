module Main where

import Core.Ast.Common
import Core.Module
import Core.Parse
import Core.Pretty
import Core.TypeCheck
import System.Exit
import Text.Megaparsec
import TypeSystem.Methods

tryParse p = do
  case p of
    Right x -> pure x
    Left error -> do
      putStrLn (errorBundlePretty error)
      exitWith (ExitFailure 1)

termMain :: IO ()
termMain = do
  stdin <- getContents
  e' <- let run (Parser p) = p in tryParse $ parse (run term) "stdin" stdin
  let e = (: []) <$> e'
  σ <- runCore (typeCheckTerm e) $ emptyState
  κ <- runCore (typeCheckType σ) $ emptyState
  putStrLn "Term Pretty: " >> prettyPrint (Internal <$ e)
  putStrLn ""
  putStrLn "Term β Pretty: " >> prettyPrint (reduce $ Internal <$ e)
  putStrLn ""
  putStrLn "Type Pretty: " >> prettyPrint σ
  putStrLn ""
  putStrLn "Kind Pretty: " >> prettyPrint κ

readModule :: String -> IO (Module Internal)
readModule path = do
  file <- readFile path
  code <- let run (Parser p) = p in tryParse $ parse (run modulex) path file
  pure (Internal <$ code)

main :: IO ()
main = do
  stdin <- getContents
  code' <- let run (Parser p) = p in tryParse $ parse (run modulex) "stdin" stdin
  let code = (: []) <$> code'
  putStrLn "Module Pretty: " >> prettyPrint (Internal <$ code)
  ordering <- order code
  typeCheckModule ordering
  putStrLn "Module β Pretty: " >> prettyPrint (unorder $ reduceModule $ (Internal <$ ordering))
  pure ()
