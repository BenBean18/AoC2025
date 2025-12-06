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

-- l should be enumerated
-- partial highestJoltage: List (Nat, Char) -> Nat -> List (Nat, Char)
-- highestJoltage _ 0 = []
-- highestJoltage l (S n) =
--     let s = reverse $ sortBy (compare `on` (\p => (the (Nat -> Int) cast) (cast (snd p) * length l) + (the (Nat -> Int) cast) (fst p))) l
--         next: List (Nat, Char) = foldl (\current, new => if and (map (\c => Delay (fst new >= fst c)) current) then current ++ [new] else current) (the (List (Nat, Char)) []) s in (trace $ show next) $
--             {-if length next >= (S n) then take (S n) next else -}sortBy (compare `on` fst) ([(last ((0, 'A') :: reverse next))] ++ highestJoltage (filter (/= (last ((0, 'A') :: reverse next))) l) n) -- first sequence where fst of the first one is less than fst of the second one

trimLeft: List (Nat, Char) -> List (Nat, Char)
trimLeft ((_, ';') :: xs) = trimLeft xs
trimLeft l = l

trimRight: List (Nat, Char) -> List (Nat, Char)
trimRight = reverse . trimLeft . reverse

partial highestJoltage: List (Nat, Char) -> Nat -> List (Nat, Char)
highestJoltage _ 0 = []
highestJoltage l' (S n) =
    -- s is the enumerated list ordered by character, e.g. 9794 --> [(2, '9'), (0, '9'), (1, '7'), (3, '4')]
    -- next is s but now indices have to be in order, so [(2, '9'), (3, '4')]
    let l = trimRight l'
        s = reverse $ sortBy (compare `on` (\p => (the (Nat -> Int) cast) (cast (snd p) * length l) - (the (Nat -> Int) cast) (fst p))) l
        next: List (Nat, Char) = foldl (\current, new => if and (map (\c => Delay (fst new >= fst c)) current) then current ++ [new] else current) (the (List (Nat, Char)) []) s
        filteredNext = filter ((flip (/=)) ';' . snd) next in -- (trace $ pack (map snd l) ++ " # " ++ show s ++ " # " ++ show filteredNext) $
            {-if length next >= (S n) then take (S n) next else -}sortBy (compare `on` fst) ([(last ((0, 'A') :: reverse filteredNext))] ++ highestJoltage (map (\s => if s == (last ((0, 'A') :: reverse filteredNext)) then (fst s, ';') else s) l) n) -- first sequence where fst of the first one is less than fst of the second one


partial part1 : String -> Int
part1 input = sum $ traceWrap $ map (cast . pack . (map snd . (flip highestJoltage) 2) . enumerate . unpack) (lines input)

-- [redacted] too low :(
-- for 9794, [(2, '9'), (0, '9'), (1, '7'), (3, '4')] is wrong! want lower indices sooner, so can sort on like (cast snd p * length l - fst p) -- now done


-- HAHA I KNEW IT

-- [redacted] too low :(

-- The problem was that we lost the original order once there was more than 2, just fixed it.

-- [redacted] still too low

-- [redacted] ALSO too low?!?

-- If there are already numbers to the right of us, then pick leftmost, else pick rightmost.

-- e.g. (max 9 inferred) 789792, should pick rightmost 9, then from (max 9) 78972 the new rightmost 9, then from (max 9) 7872 rightmost 7, then from (max 8) 782 rightmost 8, then from (max 8) 782 the leftmost 7.

-- from (max 9) 9794, pick rightmost 9, then from (max 9) 97*4 pick rightmost 9, then from (max 9) *7*4 i would pick 7 here, not enough info to contradict

partial part2 : String -> Int
part2 input = sum {-$ traceWrap-} $ map (cast . pack . (map snd . (flip highestJoltage) 12) . enumerate . unpack) (lines input)

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2