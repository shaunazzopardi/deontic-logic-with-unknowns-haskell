module DLWithUnknowns (Contract(THEN, REPBY, AND, ACTTHEN, O,P,F,U,SAT,VIOL,UNKC) 
                  ,Party
                  ,Action
                  ,startsWith) where

import Data.List

data Label = String

data Party = PARTY String | UNKP deriving(Show, Read, Eq)

data Action = ACT String | UNKA deriving(Show, Read, Eq)

data ComplexAction = ACTION Action
         | ZERO
         | ONE
                    | THENA(ComplexAction, ComplexAction)
                    | ORA(ComplexAction, ComplexAction)
                    | ANDA(ComplexAction, ComplexAction)
                    deriving(Show, Read, Eq)

data Contract = Norm
                | SAT | VIOL | UNKC
                | O(Party, Action) 
                | P(Party, Action) 
                | F(Party, Action) 
                | U(Party, Action) 
                | THEN(Contract, Contract)
                | REPBY(Contract, Contract)
                | AND(Contract, Contract)
                | ACTTHEN(ComplexAction, Contract)
                deriving(Show, Read, Eq)
                
startsWith :: Contract -> Contract
startsWith (AND(c, d)) = AND(startsWith c, startsWith d)
startsWith (THEN(c, d)) = startsWith c
startsWith (REPBY(c, d)) = startsWith c
startsWith (ACTTHEN(ca, d)) = if containsEmpty ca
                                then startsWith d
                                else ACTTHEN(ca, d)
startsWith (c) = c
                
synEquiv :: (Contract, Contract) -> Bool
synEquiv (c, d) = startsWith c == startsWith d
                    
containsEmpty :: ComplexAction -> Bool
containsEmpty ZERO = True
containsEmpty (ANDA(ca,cb)) = containsEmpty ca && containsEmpty cb
containsEmpty (ORA(ca,cb)) = containsEmpty ca || containsEmpty cb
containsEmpty (THENA(ca,cb)) = containsEmpty ca
containsEmpty ca = False


resolveAct :: (ComplexAction, [Action]) -> ComplexAction
resolveAct (ACTION a, as) = if elem a as then ZERO else ACTION a
resolveAct (ZERO, as) = ZERO
resolveAct (ONE, as) = ZERO
resolveAct (THENA(ca, cb), as) = if x == ZERO 
                                   then cb
                                   else THENA(x, cb)
                                where x = resolveAct(ca, as)
resolveAct (ORA(ca, cb), as) = if x == ZERO || y == ZERO 
    then ZERO
    else ORA(ca, cb)
 where 
     x = resolveAct(ca, as)
     y = resolveAct(cb, as)
resolveAct (ANDA(ca, cb), as) = if x == ZERO && y == ZERO
     then ZERO
     else ANDA(ca, cb)
 where 
     x = resolveAct(ca, as)
     y = resolveAct(cb, as)
 
resolve :: (Contract, [Action]) -> Contract
resolve (SAT, as) = SAT
resolve (VIOL, as) = VIOL
resolve (UNKC, as) = UNKC
resolve (U(p,a), as) = UNKC    
resolve (O(p,UNKA), as) = if as == []
                         then VIOL
                         else UNKC
resolve (O(p,a), as) = if elem a as
                 then SAT
                 else VIOL
resolve (P(p,a), as) = if elem a as
                 then SAT
                 else UNKC
resolve (F(p,UNKA), as) = if as == []
                         then UNKC
                         else VIOL
resolve (F(p,a), as) = if elem a as
                 then VIOL
                 else SAT                
resolve (THEN(c,cc), as) =  case(resolve(c, as)) of
                          SAT -> cc
                          VIOL -> VIOL
                          UNKC -> UNKC
                          ccc -> THEN(ccc, cc)
resolve (REPBY(c,cc), as) =  case(resolve(c, as)) of
                          SAT -> SAT
                          VIOL -> cc
                          UNKC -> UNKC
                          ccc -> REPBY(ccc, cc)
resolve (AND(c,cc), as) =  case(x) of
                          SAT -> resolve(cc, as)
                          VIOL -> VIOL
                          UNKC -> UNKC
                          ccc -> AND(x, resolve(cc, as))
                         where x = resolve(c, as)
resolve (ACTTHEN(ca,c), as) =  if containsEmpty(ca)
  then if cond == ZERO
           then c
           else AND(ACTTHEN(cond, c), resolve(c, as))
  else ACTTHEN(cond, c)
                         where 
  cond = resolveAct(ca, as)

resolveTrace :: (Contract, [[Action]]) -> Contract
resolveTrace (c, ass) = resolveTrace(cc, drop 1 ass)
                 where cc = resolve(c, ass!!0)
                 
conflicts :: (Contract, Contract)-> Bool
conflicts (O(p, a), F(p', a')) = if a == a'
          then True
          else False
conflicts (P(p, a), F(p', a')) = if a == a'
          then True
          else False
conflicts (AND(c, cc), ccc) = conflicts(c, cc) || conflicts(c, ccc) || conflicts(cc, ccc)
conflicts (ccc, AND(c, cc)) = conflicts(ccc, c) || conflicts(ccc, cc) || conflicts(c, cc)
conflicts (THEN(c, cc), ccc) = conflicts(c, ccc)
conflicts (ccc, THEN(c, cc)) = conflicts(c, ccc)
conflicts (REPBY(c, cc), ccc) = conflicts(c, ccc)
conflicts (ccc, REPBY(c, cc)) = conflicts(c, ccc)
conflicts (ACTTHEN(ca, c), cc) = if containsEmpty(ca)
          then conflicts(c, cc)
          else False
conflicts (cc, ACTTHEN(ca, c)) = if containsEmpty(ca)
          then conflicts(c, cc)
          else False
conflicts c = False

genAllCurrentActs :: ComplexAction -> [[Action]]
genAllCurrentActs (ACTION a) = [[a]]
genAllCurrentActs ZERO = [[]]
genAllCurrentActs ONE = [[]]
genAllCurrentActs (THENA(ca, ca')) = genAllCurrentActs(ca)
genAllCurrentActs (ORA(ca, ca')) = genAllCurrentActs(ca) ++ genAllCurrentActs(ca')
genAllCurrentActs (ANDA(ca, ca')) = cartProd (genAllCurrentActs(ca)) (genAllCurrentActs(ca'))

cartProd :: [[Action]] -> [[Action]] -> [[Action]]
cartProd xs ys = [ [] ++ x ++ y | x <- xs, y <- ys]


nextSteps :: Contract -> [[Action]]
nextSteps SAT = []
nextSteps VIOL = []
nextSteps UNKC = []
nextSteps (U(p, a)) = []
nextSteps (O(p, a)) = [[a],[]]
nextSteps (P(p, a)) = [[a],[]]
nextSteps (F(p, a)) = [[a],[]]
nextSteps (AND(c, c')) = nextSteps(c) ++ nextSteps(c')
nextSteps (REPBY(c, c')) = nextSteps(c)
nextSteps (THEN(c, c')) = nextSteps(c)
nextSteps (ACTTHEN(ca, c)) = if elem [] x
  then x ++ nextSteps(c)
  else x
                         where x = genAllCurrentActs(ca)

resolve' :: (Contract, [[Action]]) -> [Contract]
resolve' (c, as) = [ resolve(c, a) | a <- as] 


allPossTraces :: Contract -> [[[Action]]]
allPossTraces SAT = [] 
allPossTraces VIOL = [] 
allPossTraces UNKC = [] 
allPossTraces (O(p,a)) = [ [n] | n <- x]
                 where x = nextSteps(O(p,a))
allPossTraces (F(p,a)) = [ [n] | n <- x]
                 where x = nextSteps(F(p,a))
allPossTraces (P(p,a)) = [ [n] | n <- x]
                 where x = nextSteps(P(p,a))
allPossTraces (U(p,a)) = [ [n] | n <- x]
                 where x = nextSteps(U(p,a))
allPossTraces (AND(c, c')) = [x ++ y | x <- xs, y <- ys]
                         where 
  xs = allPossTraces(c)
  ys = allPossTraces(c')        
allPossTraces (REPBY(VIOL, c')) = allPossTraces(c')        
allPossTraces (REPBY(c, c')) = foldl (++) [] [ map (\z -> [x] ++ z) (allPossTraces(REPBY(resolve(c, x), c'))) | x <- xs]
  where
          xs = nextSteps(c)
allPossTraces (THEN(SAT, c')) = allPossTraces(c')
allPossTraces (THEN(c, c')) = foldl (++) [] [ map (\z -> [x] ++ z) (allPossTraces(THEN(resolve(c, x), c'))) | x <- xs]
  where
          xs = nextSteps(c)
allPossTraces (ACTTHEN(ZERO, c)) = allPossTraces(c)
allPossTraces (ACTTHEN(ONE, c)) = if x == []
          then [[[]]]
          else [ [[]] ++ y | y <- x ]
  where x = allPossTraces(ACTTHEN(ZERO, c))
allPossTraces (ACTTHEN(ca, c)) = if xEmpty
          then foldl (++) [] [map (\z -> [x] ++ z) (allPossTraces(AND(ACTTHEN(resolveAct(ca, x), c),resolve(c, x)))) | x <- xs]
          else foldl (++) [] [map (\z -> [x] ++ z) (allPossTraces(ACTTHEN(resolveAct(ca, x), c))) | x <- xs]
  where
          xs = genAllCurrentActs(ca)
          xEmpty = containsEmpty(ca)

traceConflicts :: (Contract, [[Action]]) -> Bool
traceConflicts (c, xs) = case(startsWith c) of
                            AND(cc,cc') -> conflicts(cc, cc')
                            _ -> False                            

getConflictingTraces :: Contract -> [[[Action]]]
getConflictingTraces c = [ x | x <- xs, traceConflicts (c, x)]
                        where xs = allPossTraces(c)

getSatisfyingTraces :: Contract -> [[[Action]]]
getSatisfyingTraces c = [ x | x <- xs, traceConflicts (c, x)]
                        where xs = allPossTraces(c)

---for each x in xs 
---dotProd :: [[Action]] -> [[Action]] -> [[Action]]

---CVUSTraces :: (Contract, [[Action]]) -> ([Action], [Action], [Action], [Action])---
---CVUSTraces (SAT, 
