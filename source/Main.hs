module Main where

import Core.Ast
import Core.Parse
import Core.Pretty
import qualified Data.Map as Map
import qualified Data.Set as Set
import Environment
import System.Exit
import Text.Megaparsec
import TypeSystem.Methods

tryParse p = do
  case p of
    Right x -> pure x
    Left error -> do
      putStrLn (errorBundlePretty error)
      exitWith (ExitFailure 1)

main :: IO ()
main = do
  stdin <- getContents
  e <- tryParse $ parse term "stdin" stdin
  case runCore (typeCheckLinear e :: Core SourcePos (Error SourcePos) (TypeInternal, Use)) $ CoreState Map.empty Map.empty Set.empty of
    Left f -> putStr "Error: " >> print f
    Right ((σ, _), _) -> do
      let (Right (κ, _)) = runCore (typeCheck σ :: Core Internal (Error Internal) KindInternal) $ CoreState Map.empty Map.empty Set.empty
      putStrLn "Term Pretty: " >> putStrLn (showTerm $ Internal <$ e)
      putStrLn ""
      putStrLn "Term β Pretty: " >> putStrLn (showTerm $ reduce $ Internal <$ e)
      putStrLn ""
      putStrLn "Type Pretty: " >> putStrLn (showType σ)
      putStrLn ""
      putStrLn "Kind Pretty: " >> putStrLn (showKind κ)
