module Day03

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

-- To get the maximum "joltage" (nice name btw), we need the first occurrence of the max then the highest after it, unless max is at end, then second highest then highest

enumerate: List t -> List (Nat, t)
enumerate l = zip [0..length l] l

partial highestJoltage: List Char -> Nat -> List Char
highestJoltage _ 0 = []
highestJoltage l (S n) =
    let s = reverse $ sortBy (compare `on` (\p => (the (Nat -> Int) cast) (cast (snd p) * length l) - (the (Nat -> Int) cast) (fst p))) (enumerate l)
        next: List (Nat, Char) = foldl (\current, new => if fst new >= fst (last ((0, '0') :: current)) then current ++ [new] else current) (the (List (Nat, Char)) []) s in
            if length next >= (S n) then take (S n) (map snd next) else highestJoltage (map snd (filter (/= (last ((0, 'A') :: reverse next))) s)) n ++ [snd (last ((0, 'A') :: reverse next))] -- first sequence where fst of the first one is less than fst of the second one

partial part1 : String -> Int
part1 input = sum $ map (cast . pack . ((flip highestJoltage) 2) . unpack) (lines input)

-- [redacted] too low :(
-- for 9794, [(2, '9'), (0, '9'), (1, '7'), (3, '4')] is wrong! want lower indices sooner, so can sort on like (cast snd p * length l - fst p) -- now done

-- Part 2

partial part2 : String -> Int
part2 input = 2

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2