{-|
------------------------------------------------------------------------
About this Programm:
The Software calculates a proof-tree in the System P inference System
for a given knowledge base (KB) and a given inference (A |~ C). Note
that this software runs a long time and maybe uses much memory.
Especially for large signatures the system may run out of memory,
since to set of worlds, and therfore the set of possible infereces,
grows exponentally with the size of the signature.


Licence:
Copyright 2017 Kai Sauerwald (kontakt@kai-sauerwald.de)

Permission is hereby granted, free of charge, to any person obtaining 
a copy of this software and associated documentation files 
(the "Software"), to deal in the Software without restriction, 
including without limitation the rights to use, copy, modify, merge, 
publish, distribute, sublicense, and/or sell copies of the Software, 
and to permit persons to whom the Software is furnished to do so, 
subject to the following conditions:

The above copyright notice and this permission notice shall be 
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, 
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF 
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. 
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY 
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, 
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE 
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

------------------------------------------------------------------------
How to use this Programm:

------------------------------------------------------------------------
The main idea of the Programm:
This Programm calculates iterative a closure with the rules of System P:

AND:
A |~ B       A |~ C
-------------------
   A |~ B\land C

Right Weakening (RW):
A |~ B    B \subseteq C
----------------------
        A |~ C

Cautious Monotonicity (CM):
A |~ B        A |~ C
--------------------
   A \land B |~ C

OR:
A |~ C      B |~ C
------------------
   A\lor B |~ C

Identity (Id):

------------
   A |~ A

This is a complete set of rules [1], if you view System P on the level
of models. On the level of formula, there are more rules necessary 
(like Left Logical Equivalence).

While all Id inferences are added at the start of the programm, every other Rule is applied exhaustivly, then System checks if the desired
inference is found, or the application of rules application make
no change any more.


|-}

import Data.Set (Set,fromList,union,unions,insert,singleton,toList,empty,intersection)
import Debug.Trace (trace)
import Data.List (foldl')
import System.IO (hGetContents,IOMode (ReadMode),openFile)
import qualified Data.Set as Set

{-|
How to use this Programm?

Suppose you have 
- a signature S={F,B,P}, 
- a knowledge base K={ P|~B, B|~F, P|~not F }
- and want to know if F |~ not P in System P under K holds

Have a working Haskell-Platform (ghc) available

run ghci with inference.hs:
#! ghci inference.hs
and enter
putStrLn $ genWorldDataStructure ['F','B','P']

Replace line C to Y in this file by the output of the command

Then modify the "theKB" in line Z, to enter the corresponding KB K.
In this example:
theKB = [(wPp,wBp),(wBp,wFp),(wPp,wFn)]

then modify line Z to the desired endcondition
checkEnd i = Set.member (wBp,wPn) i

While this uses some helpful some shortcuts like defined in line X to Y.
Please remove these example shortcuts in line X to Y, or modify them
for your signature and KB.

|-}

-- Helperfunction that generates the datastructures for the worlds and so on...
genWorldDataStructure :: [Char] -> String
genWorldDataStructure cs = "data World = " ++ (tail $ genSep "|") ++ " deriving (Eq,Ord,Show,Read)\n\nallWorlds :: Set World\nallWorlds = [" ++ (tail $ genSep ",") ++ "]"
    where scs :: Set (Set Char)
          scs = subsetsOf $ fromList cs
          mapped :: Set String
          mapped = Set.map doIT scs
          doIT :: Set Char -> String
          doIT s = foldl' (\str c -> str ++ [c] ++ (if Set.member c s then "p" else "n" ) ) "W" cs
          genSep :: String -> String
          genSep sep = Set.foldl' (\str w -> str ++ sep ++ w ) "" mapped

----------------------------------------
-- The following needs change
----------------------------------------
          
-- This Datastructure represents all possible Worlds
data World = WFpBpPp | WFnBpPp  | WFnBnPp | WFnBnPn | WFnBpPn | WFpBnPp | WFpBnPn | WFpBpPn deriving (Eq,Ord,Show,Read)

-- Set of all Worlds
allWorlds :: Set World
allWorlds = fromList [ WFpBpPp , WFnBpPp , WFnBnPp , WFnBnPn , WFnBpPn , WFpBnPp , WFpBnPn , WFpBpPn ]

-- The given knowledge base
theKB :: [Inference]
theKB = [(wPp,wBp),(wBp,wFp),(wPp,wFn)]

-- The endcondition
checkEnd :: Set Inference -> Bool
checkEnd i = Set.member (wFp,wPn) i

-- some shotcuts
wPp = fromList [WFpBpPp, WFnBpPp, WFnBnPp, WFpBnPp]
wPn = fromList [WFpBpPn, WFnBpPn, WFnBnPn, WFpBnPn]
wBp = fromList [WFpBpPp, WFnBpPp, WFnBpPn, WFpBpPn]
wFp = fromList [WFpBpPp, WFpBnPp, WFpBpPn, WFpBnPn]
wFn = fromList [WFnBpPp, WFnBnPp, WFnBpPn, WFnBnPn]

----------------------------------------
-- The following needs NO change
----------------------------------------

-- Datatype for inferences
type Inference = (Set World, Set World)

-- Datatype for programmsteps (the use of inferences)
-- (T,A|~B,C|~D,E|~F)
-- with the semantics: use of rule T with parameter A |~ B and C | ~D,
-- and the result E |~ F
type ProgrammStep = (String, Inference, Inference, Inference)

-- Current ProgrammState, maintains a list of all gained inferences and and how they obtained
type State = (Set Inference, [ProgrammStep])

-- Some usefull show functions
showI :: Inference -> String
showI (a,b) = "(" ++ show (toList a) ++ "," ++ show (toList b) ++ ")"

showStep :: ProgrammStep -> String
showStep (name,a,b,c) = "{" ++ name  ++ ": " ++ showI a ++ ", " ++ showI b ++ ", " ++ showI c ++ "}"

--showState :: State -> String
--showState (inf,steps) = "" ++ show inf ++ "\nSteps: " ++ showStep steps

doR :: Set World ->  Inference
doR w = (w, w) 

allFormula :: Set (Set World)
allFormula = subsetsOf allWorlds

-- Helper Functions. These generate all subsets of a set

subsetsOfN :: Ord a => Int -> Set a -> Set (Set a)
subsetsOfN n s | Set.size s < n || n < 0 = empty
               | otherwise               = Set.foldr cons nil s !! n
        where
            nil :: Ord a => [Set (Set a)]
            nil = singleton empty : repeat empty
            cons :: Ord a => a -> [Set (Set a)] -> [Set (Set a)]
            cons x sets = zipWith union sets
                               (empty : map (Set.map $ insert x) sets)

subsetsOf :: Ord a => Set a -> Set (Set a)
subsetsOf s = unions [ subsetsOfN n s | n<-[0..(Set.size s)]]

----------------------------
-- The rules of System P
rRW :: Inference -> [ProgrammStep]
rRW a@(p1,c1)  = [("rw", a, a, (p1,d)) | d <- toList allFormula, Set.isProperSubsetOf c1 d ]

rAND :: Inference -> Inference -> ProgrammStep
rAND a@(p1,c1) b@(_,c2) = ("and",a,b,(p1,intersection c1 c2))

rCM :: Inference -> Inference -> ProgrammStep
rCM a@(p1,c1) b@(_,c2) = ("cm",a,b,(intersection p1 c1,c2))
 
rOR :: Inference -> Inference -> ProgrammStep
rOR a@(p1,c1) b@(p2,_) = ("or",a,b,(union p1 p2,c1))

rR :: Set World -> ProgrammStep
rR f = ("r", (f,f),(f,f),(f,f))

initialInferences = union (fromList theKB) $ 
                    unions  [ singleton (doR w) | w <- toList allFormula, notEmpty w ] -- Insert all reflexive formula
initialSteps = [ rR w | w <- toList allFormula, notEmpty w ] ++ [("kb",i,i,i) | i<- theKB ]
initialState = (initialInferences,initialSteps)

notEmpty :: Set a -> Bool
notEmpty s = not $ Set.null s

findInference :: State -> [ProgrammStep]
findInference state@(ig,_) = if checkEnd inf then steps else (foreach1  (toList inf) $ toList inf)
    where (inf,steps) = doClosure (length ig) state
          foreach1 :: [Inference] -> [Inference] -> [ProgrammStep]
          foreach1 []   l = []
          foreach1 (x:xs) l = if foreach2 x l /= [] 
                                then foreach2 x l 
                                else 
                                    --trace ("rekursion!" ++ show (head xs) ++ ", height: " ++ show (length steps)) 
                                    (foreach1 xs l)
                           --         if trace "muh" (doTheRWStep x (inf,steps) /= [])
                           --             then doTheRWStep x (inf,steps) 
                           --             else foreach1 xs l
          foreach2 :: Inference -> [Inference] -> [ProgrammStep]
          foreach2 i1 [] = []
          foreach2 i (j:xs) = if doIt i j /= [] then doIt i j else foreach2 i xs
          doIt :: Inference -> Inference -> [ProgrammStep]
          doIt i j = doTheStep i j (inf,steps)

notContains :: Set Inference -> Inference -> Bool
notContains si i@(a,b) = notEmpty a && notEmpty b && Set.notMember i si  -- helper $ toList si
--    where helper :: [Inference] -> Bool
--          helper [] = True
--          helper (x:xs) = if x==i then False else helper xs

--doTheRWStep :: Inference -> State -> [ProgrammStep]
--doTheRWStep i@(p,c) (inf,steps) = foreach setRW
--    where setRW  = rRW i 
--          foreach :: [ProgrammStep] -> [ProgrammStep]
--          foreach [] = []
--          foreach (rwR@(_,_,_,rRe):xs) = if notContains inf rRe && (findInference (insert rRe inf, rwR:steps) /= []) then (trace "found" (rwR:steps)) else foreach xs

doClosure :: Int -> State -> State
doClosure n (inf,steps) = trace ("close: " ++ show (Set.size inf)++"," ++ show (Set.size inf2)) $ if n == (Set.size inf2) then (inf,steps) else doClosure (Set.size inf2) (inf2,steps2)
    where (inf2,steps2) = cmClosure . andClosure . rwClosure . orClosure $ (inf,steps)

rwClosure :: State -> State
rwClosure (inf,steps) = trace ("rwClosure over " ++ show (length inf)) $ foldl' foreach (inf,steps) [ i | i<- toList inf ]
    where foreach :: State -> Inference -> State
          foreach (inf2,steps2) i = ( union inf2 res2, res ++ steps2)
            where res = [ s | s@(_,_,_,r) <- (rRW i), Set.notMember r inf2]
                  res2 = fromList [ r | (_,_,_,r) <- res ]

orClosure :: State -> State
orClosure state@(inf,_) = trace ("orClosure over " ++ show (length inf)) $ foreach [ i | i <- toList inf] state
    where
        foreach :: [Inference] -> State -> State
        foreach [] s = s
        foreach (x:xs) (inf,steps) = foreach xs (inf2, steps2)
            where (inf2,steps2) = foreach2 [ j | j<- toList inf ] x (inf,steps)
        foreach2 :: [Inference] -> Inference -> State -> State
        foreach2 [] _ s = s
        foreach2 (i:xs) j (inf,steps) = foreach2 xs j $  if fullfills then (res,res2) else (inf,steps)
            where r@(_,_,_,(a,b)) = rOR i j
                  (ip,ic) = i
                  (jp,jc) = j
                  fullfills = ic==jc && notEmpty a && notEmpty b && Set.notMember (a,b) inf
                  res = Set.insert (a,b) inf
                  res2 = r:steps

andClosure :: State -> State
andClosure state@(inf,_) = trace ("andClosure over " ++ show (length inf)) $ foreach [ i | i <- toList inf] state
    where
        foreach :: [Inference] -> State -> State
        foreach [] s = s
        foreach (x:xs) (inf,steps) = foreach xs (inf2, steps2)
            where (inf2,steps2) = foreach2 [ j | j<- toList inf ] x (inf,steps)
        foreach2 :: [Inference] -> Inference -> State -> State
        foreach2 [] _ s = s
        foreach2 (i:xs) j (inf,steps) = foreach2 xs j $  if fullfills then (res,res2) else (inf,steps)
            where r@(_,_,_,(a,b)) = rAND i j
                  (ip,ic) = i
                  (jp,jc) = j
                  fullfills = ip ==jp  && notEmpty a && notEmpty b && Set.notMember (a,b) inf
                  res = Set.insert (a,b) inf
                  res2 = r:steps

cmClosure :: State -> State
cmClosure state@(inf,_) = trace ("cmClosure  over " ++ show (length inf))$ foreach [ i | i <- toList inf] state
    where
        foreach :: [Inference] -> State -> State
        foreach [] s = s
        foreach (x:xs) (inf,steps) = foreach xs (inf2, steps2)
            where (inf2,steps2) = foreach2 [ j | j<- toList inf ] x (inf,steps)
        foreach2 :: [Inference] -> Inference -> State -> State
        foreach2 [] _ s = s
        foreach2 (i:xs) j (inf,steps) = foreach2 xs j $  if fullfills then (res,res2) else (inf,steps)
            where r@(_,_,_,(a,b)) = rCM i j
                  (ip,ic) = i
                  (jp,jc) = j
                  fullfills = ip ==jp  && notEmpty a && notEmpty b && Set.notMember (a,b) inf
                  res = Set.insert (a,b) inf
                  res2 = r:steps

--orClosure :: State ->  State
--orClosure state@(inf,steps) = trace "test3"  $! foldl' foreach state  [ (i,j) | i <- toList inf, j <- toList inf]
--    where foreach :: State -> (Inference,Inference) -> State
--          foreach (inf2,steps2) (i,j) = trace "test" $! (res,res2)
--            where r@(_,_,_,(a,b)) = trace "test4" $ rOR i j
--                  res = if (trace "test5" $ notEmpty a) && notEmpty b && Set.notMember (a,b) inf2 then trace "test2" $ Set.insert (a,b) inf2 else inf2
--                  res2 = if (trace "test5" $ notEmpty a) && notEmpty b && Set.notMember (a,b) inf2 then  r:steps2 else steps2
                
   -- foldl' foreach (inf,steps) [ rOR i j | i <- toList inf, j <- toList inf <- ]
   -- where foreach :: State -> (Inference,Inference) -> State
   --       foreach (inf2,steps2) (i,j) = (trace (show$ length res) res, res2)
   --         where r@(_,_,_,(a,b)) = rOR i j
   --               res = if notEmpty a && notEmpty b && Set.notMember (a,b) inf2 then Set.insert (a,b) inf2 else inf2
   --               res2 = if notEmpty a && notEmpty b && Set.notMember (a,b) inf2 then  r:steps2 else steps2

doTheStep :: Inference -> Inference -> State -> [ProgrammStep]
doTheStep i@(p1,c1) j@(p2,c2) (inf,steps) = if (p1==p2) && (notContains inf aRe) && trace ("Rekursion(" ++ show (length steps) ++ "): " ++ showStep andR) (findInference (insert aRe inf,andR:steps) /= [])
                                            then
                                                --trace ("Finde Inference" ++ (show aRe)) 
                                                (((andR:steps))::[ProgrammStep])
                                            else
                                                if p1==p2 && notContains inf cRe &&  trace ("Rekursion(" ++ show (length steps) ++ "): " ++ showStep cmR) (findInference (insert cRe inf,cmR:steps) /= [])
                                                then 
                                                    --trace ("Finde Inference" ++ (show cRe)) 
                                                    (((cmR:steps))::[ProgrammStep])
                                                else
                                                    []
                                                   -- if c1==c2 && notContains inf oRe &&  trace ("Rekursion(" ++ show (length steps) ++ "): " ++ showStep orR) (findInference (insert oRe inf, orR:steps) /= [])
                                                   -- then
                                                   --     --trace ("Finde Inference" ++ (show oRe)) 
                                                   --     (((orR:steps))::[ProgrammStep])
                                                   -- else
                                                   --     []
    where andR@(_,_,_,aRe) = rAND i j 
          cmR@(_,_,_,cRe) = rCM i j
          orR@(_,_,_,oRe) = rOR i j

checkEnd :: Set Inference -> Bool
checkEnd i = Set.member (wBp,wPn) i
--checkEnd [] = False
--checkEnd ((name,_,_,(x,y)):xs) = if (name /= "r" && x ==wFp && y==wPn ) then True else checkEnd xs

main :: IO ()
main =  do
        print $ length initialSteps
        print $ length steps
        writeFile "result.txt" $ show result -- (foldr (\step s -> s ++ showStep step) "" result) 
        print result
        return ()        
            where (_,steps) = rwClosure initialState
                  result = findInference $ rwClosure initialState

-- handle <-  openFile "result.txt" ReadMode
-- conents <- hGetContents handle
-- steps = (read contents )::[ProgrammStep]

getSteps :: String -> [ProgrammStep]
getSteps s = (read s)::[ProgrammStep]

findAbleitung :: Inference -> [ProgrammStep] -> ProgrammStep
findAbleitung (a,b) (x@(_,_,_,t):xs) = if (a,b) == t then x else findAbleitung (a,b) xs

findAllForAbleitung :: Inference -> [ProgrammStep] -> Set ProgrammStep
findAllForAbleitung i@(z,y) steps = if z == y then Set.singleton (rR z) else  helper i Set.empty
    where 
        helper :: Inference -> Set ProgrammStep -> Set ProgrammStep
        helper j res = if Set.member step res then res else (if (typ == "r") || (typ == "kb") then Set.insert step res else res2 )
            where
                step@(typ, a, b, _) = findAbleitung j steps
                res1 = helper a (Set.insert step res)
                res2 = helper b res1

writeGraph :: [ProgrammStep] -> String
writeGraph steps = foldl' (\s1 s2 -> s1 ++ "\"" ++  s2 ++ "\"\n" ) "digraph G{" (toList notes) ++ foldl' (\s1 s2 -> s1 ++  s2 ++ "\n" ) "" (toList vertex) ++ "}"
    where 
        notes :: Set String
        notes = foldl' (\set (t,a,b,c) -> Set.unions [set, Set.singleton (showI a),Set.singleton (showI b), Set.singleton (showI c)] ) Set.empty steps
        vertex :: Set String
        vertex = foldl' (\set (t,a,b,c) -> Set.unions [set, Set.singleton ("\"" ++ showI a ++ "\" -> \"" ++ showI c ++ "\"[ label=\"" ++ t ++ "\"];"),  Set.singleton ("\"" ++showI b ++ "\" -> \"" ++ showI c ++ "\"[ label=\"" ++ t ++ "\"];")] ) Set.empty steps


main2 :: IO ()
main2 = do
    handle <-  openFile "result.txt" ReadMode
    contents <- hGetContents handle
    let steps = (read contents )::[ProgrammStep]
    let coolio = findAllForAbleitung (wFp,wPn) steps
    let out = writeGraph $ toList   coolio
    writeFile "thegraph.dot" out
    return ()
