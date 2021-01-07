module Main where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Type
import Core.Parse
import Core.Pretty
import Core.TypeCheck
import qualified Data.Map as Map
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
  e <- let run (Parser p) = p in tryParse $ parse (run term) "stdin" stdin
  case runCore (typeCheckLinear e :: Core SourcePos (Error SourcePos) (TypeInternal, Use)) $ CoreState Map.empty Map.empty Map.empty of
    Left f -> putStr "Error: " >> print f
    Right ((σ, _), _) -> do
      let (Right (κ, _)) = runCore (typeCheck σ :: Core Internal (Error Internal) KindInternal) $ CoreState Map.empty Map.empty Map.empty
      putStrLn "Term Pretty: " >> putStrLn (showItem $ Internal <$ e)
      putStrLn ""
      putStrLn "Term β Pretty: " >> putStrLn (showItem $ reduce $ Internal <$ e)
      putStrLn ""
      putStrLn "Type Pretty: " >> putStrLn (showItem σ)
      putStrLn ""
      putStrLn "Kind Pretty: " >> putStrLn (showItem κ)
