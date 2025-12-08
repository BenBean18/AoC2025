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

rangeUnion: (Int, Int) -> (Int, Int) -> List (Int, Int)
rangeUnion (l1, h1) (l2, h2) =
    if l1 <= l2 && h1 >= h2 then [(l1, h1)] -- one contained fully within the other
    else if l1 <= l2 && l2 <= h1 && h1 <= h2 then [(l1, h2)] -- first range starts lower, but second range goes higher
    else if l2 <= l1 && h2 >= h1 then [(l2, h2)] -- one contained fully within the other
    else if l2 <= l1 && l1 <= h2 && h2 <= h1 then [(l2, h1)] -- first range starts lower, but second range goes higher
    else if l1 <= l2 && h1 <= l2 then [(l1, h1), (l2, h2)] -- one range before other
    else if l2 <= l1 && h2 <= l1 then [(l1, h1), (l2, h2)] -- one range before other
    else ?sorry

ranges: List (Int, Int)
ranges = [(3, 5), (10, 14), (12, 18), (16, 20), (1, 2)]

-- Try to squish first two. If that's impossible, move one to the end.
-- [(3, 5, a), (10, 14, b), (12, 18, c), (16, 20, d), (1, 2, e)]
-- [(10, 14, ba), (12, 18, c), (16, 20, d), (3, 5, e), (1, 2, ab)]
-- [(10, 18, bca), (16, 20, d), (3, 5, e), (1, 2, ab)]
-- [(10, 20, bcda), (3, 5, e), (1, 2, ab)]
-- [(3, 5, ebcda), (1, 2, a), (10, 20, bcd)]

-- List of ([sources], (l, r))
unionOf': List (SortedSet Int, (Int, Int)) -> SortedSet Int -> List (SortedSet Int, (Int, Int))
unionOf' [] _ = []
unionOf' [r] _ = [r]
unionOf' ((sx, x) :: (sy, y) :: xs) all = if and (map (delay . (==) all . fst) ((sx, x) :: (sy, y) :: xs)) then ((sx, x) :: (sy, y) :: xs) else let unified = rangeUnion x y in if sort unified == sort [x, y] then unionOf' ([(union sx sy, (ne last) unified)] ++ xs ++ [(union sx sy, (ne head) unified)]) all else unionOf' (map (union sx sy, ) unified ++ xs) all

enumerate: List t -> List (Int, t)
enumerate l = zip [0..cast (length l)] l

expand: List (Int, Int) -> List (SortedSet Int, (Int, Int))
expand ranges = map (\p => (singleton (fst p), snd p)) (enumerate ranges)

allOf: List (Int, Int) -> SortedSet Int
allOf r = (fromList [0..cast (length r)-1])

listify: List (SortedSet Int, (Int, Int)) -> List (List Int, (Int, Int))
listify = map (\p => (Data.SortedSet.toList (fst p), snd p))

unionOf: List (SortedSet Int, (Int, Int)) -> SortedSet Int -> List (SortedSet Int, (Int, Int))
unionOf l all = let next = unionOf' l all in if sort (map snd next) == sort (map snd l) then l else unionOf (expand (map snd next)) all

-- map (\p => (show $ Data.SortedSet.toList (fst p), snd p)) (unionOf (map (\p => (singleton (fst p), snd p)) (enumerate ranges)) (fromList [0..cast (length ranges)]))
spanOfRange: (Int, Int) -> Int
spanOfRange (l, h) = h - l + 1

partial part2 : String -> Int
part2 input =
    let (ranges' :: ids' :: []) = forget (splitOn "" (lines input))
        ranges = sort $ map parseRange ranges'
        deduplicatedRanges = unionOf' (map (\p => (singleton (fst p), snd p)) (enumerate ranges)) (fromList [0..cast (length ranges) - 1]) in {-(trace $ show deduplicatedRanges) $ -}sum (map (spanOfRange . snd) deduplicatedRanges)

-- [REDACTED] is too low
-- [REDACTED] is too high
-- [REDACTED] is correct

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2