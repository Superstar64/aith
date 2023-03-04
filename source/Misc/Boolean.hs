module Misc.Boolean where

import Data.Bifunctor (first)
import Data.List (sortOn)
import Data.Set (Set, union, (\\))
import qualified Data.Set as Set

-- Embedding Boolean Expressions into Logic Programming
-- https://core.ac.uk/download/pdf/82206645.pdf

-- https://github.com/Superstar64/Boolean_Unification

-- polynomial of boolean ring
-- represented as sums of products of variables

data Variable x v
  = Flexible v
  | Constant x
  deriving (Show, Eq, Ord)

newtype Polynomial x v = Polynomial (Set (Set (Variable x v)))
  deriving (Show)

instance (Ord x, Ord v) => Num (Polynomial x v) where
  -- 0 is false, 1 is true
  fromInteger n =
    if even n
      then Polynomial Set.empty
      else Polynomial $ Set.singleton Set.empty

  -- logical and
  Polynomial a * Polynomial b = sum $ do
    a' <- Set.toList a
    b' <- Set.toList b
    pure $ Polynomial $ Set.singleton $ Set.union a' b'

  -- logical xor
  Polynomial a + Polynomial b = Polynomial $ (a \\ b) `union` (b \\ a)
  abs = id
  negate = id
  signum _ = 1

factor x (Polynomial e) =
  ( Polynomial $ Set.map (Set.delete x) $ Set.filter (Set.member x) e,
    Polynomial $ Set.filter (Set.notMember x) e
  )

variable x = Polynomial $ Set.singleton $ Set.singleton $ Flexible x

constant x = Polynomial $ Set.singleton $ Set.singleton $ Constant x

substitute (x, ex) (Polynomial e) = sum (map mul $ Set.toList e)
  where
    mul e = product (map apply $ Set.toList e)
      where
        apply (Flexible x') | x == x' = ex
        apply e = Polynomial $ Set.singleton $ Set.singleton e

freeVariables (Polynomial e) = Set.fromList $ do
  e' <- Set.toList e
  e'' <- Set.toList e'
  case e'' of
    Flexible x -> [x]
    Constant _ -> []

solveStep x e =
  let (t1, t2) = factor (Flexible x) e
   in ((t1 + 1) * t2, (t1 + 1) * variable x + t2)

combine problem = product (map (+ 1) problem) + 1

split x problem = (filter (Set.member x . freeVariables) problem, filter (Set.notMember x . freeVariables) problem)

solveImpl :: (Ord v, Ord x) => [v] -> [Polynomial x v] -> ([(v, Polynomial x v)], [Polynomial x v])
solveImpl [] problem = ([], problem)
solveImpl xs problem =
  let (x, (simple, problem')) = head $ sortOn (length . fst . snd) $ map (\x -> (x, split x problem)) xs
      (simple', answer) = solveStep x (combine simple)
   in first ((x, answer) :) $ solve (filter (/= x) xs) (simple' : problem')

solve xs problem = solveImpl xs (filter (\(Polynomial e) -> not $ Set.null e) problem)

renameAnswers _ [] = pure []
renameAnswers fresh ((x, e) : θ) = do
  x' <- fresh x
  ((x, substitute (x, variable x') e) :) <$> renameAnswers fresh θ

backSubstitute [] = []
backSubstitute ((x, e) : θ) =
  let θ' = backSubstitute θ
   in (x, foldr substitute e θ') : θ'
