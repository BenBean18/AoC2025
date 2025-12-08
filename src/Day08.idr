module Day08

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

parseCoordinate: String -> List Double
parseCoordinate = map cast . forget . split (== ',')

squaredDistanceBetween: List Double -> List Double -> Double
squaredDistanceBetween p1 p2 = sum (map (\x => x*x) (zipWith (-) p2 p1))

distancesBetween: List (List Double) -> List (Double, (List Double, List Double))
distancesBetween l = (concatMap (\p1 => concatMap (\p2 => if p1 < p2 then [(squaredDistanceBetween p1 p2, (p1, p2))] else []) l) l)

-- if in a set then add and exit
-- if not in a set then 
-- addToCircuits: List (SortedSet (List Double)) -> (List Double, List Double) -> List (SortedSet (List Double))
-- addToCircuits [] (p1, p2) = [fromList [p1, p2]]
-- addToCircuits (x :: xs) (p1, p2) = if contains p1 x && p1 /= p2 then insert p2 x :: addToCircuits xs (p1, p1) else if contains p2 x && p1 /= p2 then insert p1 x :: addToCircuits xs (p2, p2) else x :: addToCircuits xs (p1, p2)

-- misread the problem, didn't realize they all start in their own circuit. this is definitely a graph problem.

-- wait, if we have (a, b, c, d) and unify ab and don't deduplicate, then we get (a, b, ab, c, d) -- multiplying by 1 doesn't change anything
-- then add a to c, we have (ac, b, abc, c, d)...this is a problem. we do need to deduplicate

addToCircuits: List (SortedSet (List Double)) -> (List Double, List Double) -> List (SortedSet (List Double))
addToCircuits groups (p1, p2) =
    let groupWithLeft = ne head (filter (contains p1) groups)
        groupWithRight = ne head (filter (contains p2) groups)
        newGroup = groupWithLeft `union` groupWithRight in newGroup :: (filter (\g => g /= groupWithLeft && g /= groupWithRight) groups)

partial part1 : String -> Int
part1 input =
    let points = map parseCoordinate (lines input)
        pairs = distancesBetween points
        sortedPairs = map snd (sortBy (compare `on` fst) pairs)
        circuits = foldl addToCircuits (map singleton points) (take 1000 sortedPairs)
        lengths = reverse (sort (map (cast . length . Data.SortedSet.toList) circuits))
        in (trace $ show lengths) $ foldl (*) 1 (take 3 lengths)

-- Part 2

partial addToCircuitsUntilEnd: List (SortedSet (List Double)) -> List ((List Double, List Double)) -> (List Double, List Double)
addToCircuitsUntilEnd groups (pair :: pairs) = 
    let next = addToCircuits groups pair in
        if length next == 1 then pair
        else addToCircuitsUntilEnd next pairs

partial part2 : String -> Int
part2 input =
    let points = map parseCoordinate (lines input)
        pairs = distancesBetween points
        sortedPairs = map snd (sortBy (compare `on` fst) pairs)
        lastEdge = addToCircuitsUntilEnd (map singleton points) sortedPairs
        in cast $ sum $ (uncurry (zipWith (*))) (map (take 1) lastEdge)

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2