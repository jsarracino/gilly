module Gilly.Grammar

import Data.SortedMap as M
import Data.SortedSet as S
import Text.PrettyPrint.WL as PP

import Gilly.Util

%default total
%access public export

data Atom = Chr Char | Var String
data Prod = Snt (List Atom)
data Gram = Grm (SortedMap String (List Prod))

implementation Eq Atom where
  (Chr c) == (Chr c') = c == c'
  (Var s) == (Var s') = s == s'
  _ == _ = False

implementation Ord Atom where
  compare (Chr c) (Chr c') = compare c c'
  compare (Var v) (Var v') = compare v v'
  compare (Chr _) (Var _) = LT
  compare (Var _) (Chr _) = GT

interface Pretty a where 
  pretty : a -> Doc

-- implementation Pretty a => Show a where
--   show : a -> Str
--   show = toString . pretty

implementation Pretty Atom where
  pretty (Chr c) = char c
  pretty (Var s) = literal s
implementation Pretty Prod where
  pretty (Snt as) = cat $ map pretty as
implementation Pretty Gram where
  pretty (Grm prods) = vcat $ map (\(v, rhss) => literal v |++| literal "::=" |++| encloseSep empty empty (char '|') (map pretty rhss)) (toList prods)

implementation Show Prod where
  show = toString . pretty

implementation Show Atom where
  show = toString . pretty

implementation Show Gram where
  show = toString . pretty


first : Gram -> SortedSet Char
first = ?hFirst

follow : Gram -> SortedSet Char
follow = ?hFollow

-- convert the grammar to a bunch of locations
-- for each location, make a label

-- Inter: production name, index into alternations, index into sentence
-- Process: the root work label
-- Exter: jump to top level production
data Label = Inter String Nat Nat | Process | Exter String

implementation Eq Label where
  Process == Process                    = True
  (Exter s1) == (Exter s2)              = s1 == s2
  (Inter s1 a1 b1) == (Inter s2 a2 b2)  = s1 == s2 && a1 == a2 && b1 == b2
  _ == _ = False

implementation Ord Label where
  compare a b with (a == b)
    | True = EQ
    | False = case (a, b) of 
      (Process, _) => LT
      (_, Process) => GT
      (Inter _ _ _, Exter _) => LT
      (Exter _, Inter _ _ _) => GT
      (Exter s1, Exter s2) => compare s1 s2
      (Inter s1 a1 b1, Inter s2 a2 b2) => case (compare s1 s2, compare a1 a2, compare b1 b2) of 
        (LT, _, _) => LT
        (GT, _, _) => GT
        (_, LT, _) => LT
        (_, GT, _) => GT
        (_, _, x) => x

implementation Pretty Label where
  pretty Process = literal "$worker"
  pretty (Exter prod) = literal prod
  pretty (Inter s a b) = literal s <+> brackets (nat a) <+> brackets (nat b)


buildLabs: Gram -> List Label
buildLabs (Grm prods) = proc ++ names ++ inners
  where
    proc = [Process]
    names = map Exter (keys prods)
    inners = 
      concat $ map (\(lhs, alts) => 
        concat $ map (\(Snt as, outer) => 
          map (\(_, inner) => Inter lhs outer inner) (indices as)
          ) 
        (indices alts))
      (toList prods)
    

data Cmd = Push Label | Pop | Shift Char | Seq Cmd Cmd | Skip

implementation Pretty Cmd where
  pretty (Push l) = literal "push" |++| pretty l
  pretty Pop = literal "pop"
  pretty (Shift c) = literal "shift" |++| char c
  pretty (Seq x y) = pretty x |++| char ';' |++| pretty y
  pretty Skip = literal "skip"

-- TODO: 
operationalize : String -> Nat -> Nat -> Prod -> List (Label, (Cmd, Label))
operationalize p alt depth (Snt []) = [(Inter p alt depth, (Pop, Process))]
operationalize p alt depth (Snt ((Chr c)::xs)) = [(Inter p alt depth, (Shift c, Inter p alt (S depth)))] ++ operationalize p alt (S depth) (assert_smaller (Snt ((Chr c)::xs)) (Snt xs))
operationalize p alt depth (Snt ((Var v)::xs)) = [(Inter p alt depth, (Push (Inter p alt (S depth)), Exter v))] ++ operationalize p alt (S depth) (assert_smaller (Snt ((Var v)::xs)) (Snt xs))

Automaton : Type
Automaton = SortedMap Label (List (Cmd, Label))


buildAuto : Gram -> Automaton
buildAuto (Grm prods) = fromList $ topLevel ++ interiors
  where
    topLevel = map (\(v, alts) => (Exter v, map (\(_, k) => (Skip, Inter v k 0)) (indices alts))) (toList prods)

    interiors : List (Label, (List (Cmd, Label)))
    interiors = concat $ map (\(v, alts) => 
      concat $ map (\(alt, k) => 
        map (\(a, t) => (a, [t])) (operationalize v k 0 alt)
      ) (indices alts)
    ) (toList prods)
