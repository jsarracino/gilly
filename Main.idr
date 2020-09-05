module Main

import Gilly.Grammar
import Gilly.Util
import Gilly.Parser
-- import Gilly.NaiveGLL
import Gilly.Interpreter

import Data.SortedMap
import Data.SortedSet

plus : Prod
plus = Snt [Var "E", Chr '+', Var "E"]

times : Prod
times = Snt [Var "E", Chr '*', Var "E"]

int : Prod
int = Snt [Chr '1']

expr : Gram
expr = Grm $ fromList [("E", [plus, times, int])]
-- expr = Grm $ fromList [("E", [int])]

exprAuto : Automaton
exprAuto = buildAuto expr

-- states : List GlobalState 
-- states = filterStates (stepStates (unpack "1+1") 0 [] [(Shift '1', Process)]) empty

-- parseExpr : String -> Bool
-- parseExpr inp = parse inp "E" exprAuto

main : IO ()
main = do
  print "Hello, world!"


