module Day2

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

-- Strategy: only ranges that contain numbers with an even number of digits matter (i.e. the start OR the end is even digits)
-- Let's use 100-1466 for an example. It has 1010, 1111, 1212, 1313, 1414.
-- Take the first and second halves of the even part of the range (so floor division by 10^(digits / 2)), call them aa and bb here (since 2 digits each)
-- Greatest lower bound is max(min(aa), min(bb)) = max(10, 00) = 10
-- Lowest upper bound is min(max(aa), max(bb)) = min(14, 99) = 14
-- Total number is (lowest upper bound - greatest lower bound + 1)

-- But finding lower and upper bounds here seems annoying, so just iterate through the left half and check if the resulting number is in the set

power: Num t => t -> Int -> t
power x 0 = 1
power x n = x * power x (n-1)

log: Integral t => Eq t => t -> t -> t
log base num = if (num `div` base) == num then (-1) else 1 + log base (num `div` base)

digitsOf: Integral t => Eq t => t -> t
digitsOf num = 1 + log 10 num

leftHalfRoundDown: Integral t => Eq t => Cast t Int => t -> t
leftHalfRoundDown num = num `div` power 10 ((digitsOf (cast num) + 1) `div` 2) -- +1 is to round up denominator, so fewer digits

leftHalfRoundUp: Integral t => Eq t => Cast t Int => t -> t
leftHalfRoundUp num = num `div` power 10 ((digitsOf (cast num)) `div` 2)

duplicate: Integral t => Eq t => Cast t Int => t -> t
duplicate num = num + num * power 10 (digitsOf (cast num))

numbersForRange: Integral t => Eq t => Cast t Int => Range t => Ord t => t -> t -> List t
numbersForRange leftBound rightBound = 
    let candidates = map duplicate [leftHalfRoundDown leftBound..leftHalfRoundUp rightBound] in -- filter ((== 0) . ((flip mod) 2) . digitsOf)
        filter (\c => c >= leftBound && c <= rightBound) candidates

parseRange: String -> (Int, Int)
parseRange s = let splot = splitOn '-' (unpack s) in (cast (pack (head splot)), cast (pack (last splot)))

-- [redacted] is too low, we are not cooking
-- this is the problem, was calculating bounds wrong
-- Day2> numbersForRange 200 1999
-- [1919]

-- leftHalf 200 should return 2 not 20, then it works

-- ...[redacted] is still too low

-- Day2> numbersForRange 8884 16221
-- [8888]

-- oops, need to round down on left and round up on right

-- got it correct now :)

partial part1 : String -> Int
part1 input = sum $ concat $ map (uncurry numbersForRange . parseRange) (map pack (splitOn ',' (unpack input)))

-- Part 2

partial part2 : String -> Int
part2 input = 2

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2