module Day05

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

partial twoListToPair: List a -> (a, a)
twoListToPair (x :: y :: []) = (x,y)

partial parseRange: String -> (Int, Int)
parseRange = twoListToPair . map cast . forget . split (== '-')

isInRange: (Int, Int) -> Int -> Bool
isInRange (start, end) test = test >= start && test <= end

partial part1 : String -> Int
part1 input =
    let (ranges' :: ids' :: []) = forget (splitOn "" (lines input))
        ranges = map parseRange ranges'
        testFunction = or . flip map ranges . (delay .) . (flip isInRange)
        ids: List Int = map cast ids' in cast (length (filter testFunction ids))

-- Part 2

partial part2 : String -> Int
part2 input = 2

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2