import Gilly.Grammar

import Data.SortedSet
import Data.SortedMap

import Gilly.Util

%default total
%access public export

Sentence : Type
Sentence = List Atom


Cache : Type
Cache = SortedSet (Nat, String)

State : Type
State = (Sentence, Cache)

Forest : Type
Forest = List State


growSentence : Gram -> Nat -> State -> List State
growSentence g@(Grm prods) idx (sent, expanded) = case sent of 
  [] => [([], expanded)]
  ((Chr c) :: rest) => 
    let new = assert_total (growSentence g (S idx) (rest, expanded)) in 
      map (\(snt, cache) => ((Chr c) :: snt, cache)) new
  ((Var v) :: rest) => if contains (idx, v) expanded 
    then [] 
    else case lookup v prods of 
      Just alts =>  map (\(Snt alt) => (alt ++ rest, insert (idx, v) expanded)) alts
      Nothing => []

-- conservatively check if a sentence could be a derivation for a string prefix
checkSentenceConserv : Nat -> (List Char) -> State -> Bool
checkSentenceConserv _ [] ([], _) = True
checkSentenceConserv _ [] (_, _) = False
checkSentenceConserv _ _ ([], _) = False
checkSentenceConserv idx (c :: cs) (sent, expanded) = case sent of 
  [] => False
  ((Chr c') :: sent') => if c == c' then checkSentenceConserv (S idx) cs (sent', expanded) else False
  ((Var v) :: _) => not $ contains (idx, v) expanded

-- checkSentenceExact : (List Char) -> Nat -> Sentence -> Bool
-- checkSentenceExact [] _ [] = True
-- checkSentenceExact _ Z _ = True
-- checkSentenceExact (c :: cs) (S k) sent = case sent of 
--   [] => False
--   ((Chr c') :: sent') => if c == c' then checkSentenceExact cs k sent' else False
--   ((Var _) :: _) => False

-- growSentencesOne : Gram -> Cache -> Forest -> Forest
-- growSentencesOne g expanded sentences = 


growSentences : Gram -> List Char -> Forest -> Forest
growSentences g str states = nub  $ concat $ map (growSentence g 0) states

growIter : Gram -> List Char -> Nat -> Forest -> Forest
growIter g str Z states = states
growIter g str (S k) states = growIter g str k $ growSentences g str states

init : String -> Gram -> Forest
init v (Grm prods) = case lookup v prods of 
  (Just alts) => map (\(Snt x) => (x, empty)) alts
  Nothing => []

partial
fixedPoint : Gram -> List Char -> Nat -> Forest -> (Forest, Nat)
fixedPoint g str x forest = let nxt = growSentences g str forest in 
  if listSubEq nxt forest then (forest, x) else fixedPoint g str (S x) nxt

partial
parse : Gram -> String -> String -> (Forest, Nat)
parse g start str = fixedPoint g (unpack str) Z (init start g)