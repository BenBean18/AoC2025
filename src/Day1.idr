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

partial parseInstruction' : List Char -> Int -> Int
parseInstruction' (c :: xs) = (flip mod) 100 . (flip (if c == 'L' then (-) else (+))) (cast (pack xs))

partial parseInstruction : String -> Int -> Int
parseInstruction = parseInstruction' . unpack

executeInstruction : (Int, Int) -> (Int -> Int) -> (Int, Int)
executeInstruction (pos, zeroes) f = (f pos, if f pos == 0 then (zeroes + 1) else zeroes)

partial part1 : String -> Int
part1 input = snd $ (foldl executeInstruction (50, 0) (map parseInstruction (lines input)))

-- "to prepare for landing, close your tray table and put away things SO SAD

-- Part 2

partial part2 : String -> Int
part2 input = 2

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2