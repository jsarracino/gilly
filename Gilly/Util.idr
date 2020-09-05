module Gilly.Util

import Data.SortedSet

%default total
%access public export

indices : List a -> List (a, Nat)
indices [] = []
indices (x::xs) = (x, Z) :: (map (\(p, t) => (p, S t)) $ indices xs)

subset : SortedSet a -> SortedSet a -> Bool
subset l r = all (\x => contains x r) l

implementation Eq (SortedSet a) where
  l == r = (subset l r) && (subset r l)

listSubset : Eq a => List a -> List a -> Bool
listSubset l r = all (\x => elem x r) l

listSubEq : Eq a => List a -> List a -> Bool
listSubEq l r = (listSubset l r) && (listSubset r l)