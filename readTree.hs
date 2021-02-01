--{-# LANGUAGE TypeSynonymInstances #-}
--{-# LANGUAGE FlexibleInstances #-}
import Data.Set (Set,fromList,union,unions,insert,singleton,toList,empty,difference)
import Debug.Trace (trace)
import Data.List (foldl')
import qualified Data.Set as Set

data World = WFpBpPp | WFnBpPp  | WFnBnPp | WFnBnPn | WFnBpPn | WFpBnPp | WFpBnPn | WFpBpPn deriving (Eq,Ord,Show)

type Inference = (Set World, Set World)

showI (a,b) = "(" ++ show (toList a) ++ "," ++ show (toList b) ++ ")"

type ProgrammStep = (String, Inference, Inference, Inference)

showStep :: ProgrammStep -> String
showStep (name,a,b,c) = "{" ++ name  ++ ": " ++ showI a ++ ", " ++ showI b ++ ", " ++ showI c ++ "}"

type State = (Set Inference, [ProgrammStep])



