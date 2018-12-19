-- Constant is a synonym for String.
type Constant = String

-- definition for a Formula:
data Formula = TT                           -- truth
             | FF                           -- falsehood
             | AND Formula Formula          -- conjunction
             | IMPLIES Formula Formula      -- implication
             | CONST Constant               -- atomic proposition
             deriving (Eq, Show)

-- Some example constants
cA = CONST "A"
cB = CONST "B"
cC = CONST "C"
cD = CONST "D"
cE = CONST "E"
cF = CONST "F"

-- Some example formulas that you can use to test your functions
formula1 = IMPLIES (AND cA cB) cC
formula2 = IMPLIES FF (AND cA cB)
formula3 = IMPLIES (AND cA cB) TT
formula4 = AND (IMPLIES cA (AND cB cC)) (AND cD cE)
formula5 = AND cA cB
formula6 = IMPLIES cA cB

-- An Assignment is a list of pairs corresponding to a truth value (i.e. True or False) for each Constant in a formula
type Assignment = [(Constant, Bool)]

-- A TruthTable is an enumeration of all combinations of truth value assignments for a given formula, paired with the
-- corresponding evaluation of that formula.
data TruthTable = TruthTable [(Assignment, Bool)]

-- This function is here so that when you print a TruthTable in GHCi, the table is nice and readable.
instance Show TruthTable where
  show (TruthTable rows) =
    case rows of
      [] -> ""
      ([], result) : _ -> "   result is " ++ pad_show result ++ "\n"
      ((c,b) : as, result) : xs ->
        c ++ "=" ++ (pad_show b) ++ "   "
          ++ show (TruthTable [(as,result)])
          ++ show (TruthTable xs)
    where
      pad_show True  = "True "
      pad_show False = "False"

{-Traverse a formula and build a list of all CONSTs in the formula, without duplicates.
  Applied to a Formula and a (usually empty) list.
  The list parameter can be thought of as an accumulator to build up the list of CONSTs.
-}
getCONSTs :: Formula -> [Constant] -> [Constant]
getCONSTs TT              cList = cList
getCONSTs FF              cList = cList
getCONSTs (CONST c)       cList = nub ([c] ++ cList)
getCONSTs (AND q1 q2)     cList = nub ((getCONSTs q1 []) ++ (getCONSTs q2 []) ++ cList)
getCONSTs (IMPLIES q1 q2) cList = nub ((getCONSTs q1 []) ++ (getCONSTs q2 []) ++ cList)

--  Build a list of all possible truth assignments for a set of constants
getAssignments :: [Constant] -> [Assignment]
condense ::[Assignment] -> Assignment -> [Assignment]
getAssignments []       = [[]]
getAssignments (c : cs) = (condense (getAssignments cs) [(c,True)]) ++ (condense (getAssignments cs) [(c,False)])
condense [] c = []
condense (a:as) c = [a++c] ++ condense as c

--  Evaluate a formula with a particular truth assignment,
--   returning the resulting boolean value
evalF :: Formula -> Assignment -> Bool
evalF TT              _  = True
evalF FF              _  = False
evalF (CONST c)       as = findAssignment c as
evalF (AND q1 q2)     as = (evalF q1 as) && (evalF q2 as)
evalF (IMPLIES q1 q2) as = if (not(evalF q1 as)) || (evalF q2 as) then True
                            else False

findAssignment c [] = False
findAssignment c (a:as) = if fst a == c then snd a
                            else findAssignment c as
-- buildTable:
--  Build a truth table for a given formula.
--  You can use this function to help check your definitions
--  of getCONSTs, getAssignments and evalF.
buildTable :: Formula -> TruthTable
buildTable q =
  let assignments = getAssignments (getCONSTs q [])
  in
    TruthTable (zip assignments
                    (map (evalF q) assignments))


-- a Context is a list of Formulas, representing assumptions
member :: Formula -> [Formula] -> Bool
member x [] = False
member x (y:ys) =
  if x==y then True
    else member x ys
-- prove ctx p:
--   return True if, assuming everything in ctx is true, the formula p is true
--   otherwise, return False.
type Context = [Formula]
prove :: Context -> Formula -> Bool
prove ctx p =
  let decomposed = decompose ([],ctx)
  in
      if member p decomposed then True

    else prove_right decomposed p

-- decompose (ctx1, ctx2)
--  move through ctx2, decomposing ANDs into standalone assumptions
--                     and eliminating IMPLIESes where possible
-- invariants:
--  - ctx1 is completely decomposed (no formula in ctx1 is (AND _ _))
--  - ctx2 is a "queue" of assumptions to decompose
decompose :: (Context, Context) -> Context
decompose (ctx1, [])            = ctx1
decompose (ctx1, middle : ctx2) =
  case middle of
    AND q1 q2     -> decompose(ctx1,[q1] ++ [q2]++ ctx2)
    IMPLIES q1 q2 -> if (prove (ctx1++ctx2) q1) then decompose (ctx1++[q2], ctx2)
                       else decompose (ctx1++[middle], ctx2)
    middle        -> decompose (ctx1 ++ [middle], ctx2)

-- prove_right:
--  assuming the context is decomposed, break down the goal formula
prove_right :: Context -> Formula -> Bool

prove_right ctx TT            = True     -- TT-Right

prove_right ctx (AND p q)     = (prove ctx p) && (prove ctx q)
  -- try to apply AND-Right

prove_right ctx (IMPLIES p q) = prove (ctx ++ [p]) q
  -- try to apply IMPLIES-Right

prove_right ctx p             = False
  -- couldn't apply any of the -Right rules, so give up


prop_imp1 = prove [IMPLIES cB cC] (IMPLIES cB cC)
prop_imp2 = prove [IMPLIES cB cC] (IMPLIES (AND cB cB) cC)
prop_imp3 = not (prove [IMPLIES (AND cB cD) cC] (IMPLIES cB cC))
p1= prove [AND (CONST "B") (CONST "B")]  (CONST "B")
{- for human:
B->C |- B->C True
B->C |- (B^B)->C
not [ (B^D)->C |- B->C ]
-}
