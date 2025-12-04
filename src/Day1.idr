module Day1

import Data.String
import Data.List
import Debug.Trace
import Data.Fin
import Data.Nat
import Utilities
import Data.SortedMap
import Data.SortedSet
import Data.List1
import Data.Vect

-- Part 1

data DialState : Type where
    State : Int -> Int -> DialState

pos : DialState -> Int
pos (State p _) = p

zeroes : DialState -> Int
zeroes (State _ z) = z

partial parseInstruction' : List Char -> Int -> Int
parseInstruction' (c :: xs) = (flip mod) 100 . (flip (if c == 'L' then (-) else (+))) (cast (pack xs))

partial parseInstruction : String -> Int -> Int
parseInstruction = parseInstruction' . unpack

executeInstruction : DialState -> (Int -> Int) -> DialState
executeInstruction (State pos zeroes) f = 
    let next = f pos in State next (if next == 0 then (zeroes + 1) else zeroes)

partial part1 : String -> Int
part1 input = zeroes (foldl executeInstruction (State 50 0) (map parseInstruction (lines input)))

-- this would be fun: https://blog.cofree.coffee/2020-12-22-finally-modular-arithmetic/

-- Part 2

-- between 6055 and 6483
-- 6896 also too high
-- 6594 is wrong and now I'm slower locked wtf

-- it is NOT 6483. i am very confused.

-- this is just how many times it wraps around

-- 2, L3
-- 2 to -1 to 99
-- 99 - (-1) `mod` 100 = 1, correct

-- 2, L2
-- 2 to 0 to 0
-- 0 - 0 `mod` 100 = 0, wrong

-- but 98, R2
-- 98 to 100 to 0
-- 100 - 0 `mod` 100 = 0, correct. hmm

addWithWraparound': Nat -> Nat -> (Nat, Nat)
addWithWraparound' 0 b = (b, 0)
addWithWraparound' (S a) b = if b == 99 then
    let next = addWithWraparound' a 0 in (fst next, 1 + snd next)
    else addWithWraparound' a (S b)

subWithWraparound': Nat -> Nat -> (Nat, Nat)
subWithWraparound' 0 b = (b, 0)
subWithWraparound' (S a) 1 = let next = subWithWraparound' a 0 in (fst next, 1 + snd next) -- off by one is so fun
subWithWraparound' (S a) 0 = subWithWraparound' a 99
subWithWraparound' (S a) (S b) = subWithWraparound' a b

subWithWraparound: Nat -> Nat -> (Nat, Nat)
subWithWraparound a b = let (p, z) = subWithWraparound' a b in (trace $ "L" ++ show (a) ++ " for " ++ show (b) ++ " --> (" ++ show p ++ ", " ++ show z ++ ")") $ (p,z) 

addWithWraparound: Nat -> Nat -> (Nat, Nat)
addWithWraparound a b = let (p, z) = addWithWraparound' a b in (trace $ "R" ++ show (a) ++ " for " ++ show (b) ++ " --> (" ++ show p ++ ", " ++ show z ++ ")") $ (p,z) 

partial parseInstruction2 : DialState -> List Char -> DialState -- fold friendly!
parseInstruction2 (State pos zeroes) (c :: xs) =
    let delta = (if c == 'L' then (-1) else (1)) * (cast (pack xs))
        unmoddedNext = pos + delta
        moddedNext = unmoddedNext `mod` 100
        numberWraps' = abs (unmoddedNext - moddedNext) `div` 100 + (if moddedNext == 0 && unmoddedNext == 0 then 1 else 0)
        numberWraps = if numberWraps' > 0 then numberWraps' else 0 in (trace $ "p" ++ show moddedNext ++ " " ++ show unmoddedNext ++ " " ++ show numberWraps) $ State moddedNext (zeroes + numberWraps)

partial parseInstruction3 : DialState -> List Char -> DialState -- fold friendly!
parseInstruction3 (State pos zeroes) ('L' :: xs) = let (newPos, newZeroes) = subWithWraparound (cast (pack xs)) (cast pos) in State (cast newPos) (cast newZeroes + zeroes)
parseInstruction3 (State pos zeroes) ('R' :: xs) = let (newPos, newZeroes) = addWithWraparound (cast (pack xs)) (cast pos) in State (cast newPos) (cast newZeroes + zeroes)

partial part2 : String -> Int
part2 input = zeroes (foldl parseInstruction3 (State 50 0) (map unpack (lines input)))

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2