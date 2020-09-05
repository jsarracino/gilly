module Gilly.NaiveGLL

import Gilly.Grammar

import Data.SortedSet
import Data.SortedMap

%default total
%access public export

-- index into string, label
ParseState : Type
ParseState = (Nat, Label)

-- -- current index
-- data GlobalState = GSt (Nat, List ParseState)

GlobalState : Type
GlobalState = (ParseState, List ParseState)

StateCache: Type
StateCache = SortedSet ParseState

-- current states and stacks
WorkList : Type
WorkList = List GlobalState

partial
stepState : (List Char) -> Nat -> List ParseState -> Cmd -> Maybe (Nat, List ParseState)
stepState str idx callStack (Shift c) = case index' idx str of 
  Just c' => if c' == c then Just (S idx, callStack) else Nothing
  Nothing => Nothing 
stepState _ idx callStack (Push l) = Just (idx, (idx, l) :: callStack)
stepState _ idx callStack Pop = Just (idx, callStack) -- huh, small hack
stepState _ idx callStack Skip = Just (idx, callStack)

partial
stepStates : List Char -> Nat -> List ParseState -> List (Cmd, Label) -> List GlobalState
stepStates str idx callStack bodies = concat $ map worker bodies
  where
    worker (cmd, ret) = case stepState str idx callStack cmd of 
      Just (idx', stk') => case (ret, stk') of 
        (Process, ((_, caller) :: stk'')) => [((idx', caller), stk'')]
        (_, _) => [((idx', ret), stk')]
      Nothing           => []

filterStates : List GlobalState -> StateCache -> List GlobalState
filterStates cands seen = filter (\(c, _) => not (contains c seen)) cands


partial
interpStates : (List Char) -> Automaton -> StateCache -> WorkList -> Maybe ()
interpStates _ _ _ [] = Nothing 
interpStates str auto seen (((idx, label), callStack) :: rest) = if idx >= length str then Just () else recur
  where
    recur = case lookup label auto of 
      Just bodies =>  let 
        candStates = stepStates str idx callStack bodies
        uniqueStates = filterStates candStates seen 
        in interpStates str auto (union seen (fromList (map fst uniqueStates))) (rest ++ uniqueStates)
      Nothing => interpStates str auto seen rest

partial
runAuto : (List Char) -> Automaton -> Label -> Maybe ()
runAuto str auto start = interpStates str auto (fromList [(0, start)]) [((0, start), [])] 
-- interpAuto : Automaton -> List GlobalState -> 

parse : String -> String -> Automaton -> Bool
parse input start auto = case runAuto (unpack input) auto (Exter start) of 
  Just () => True
  Nothing => False