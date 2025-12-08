module Day04

import Data.String
import Data.List
import Debug.Trace
import Data.Fin
import Data.Nat
import Utilities
import Data.SortedMap
import Data.SortedSet
import Data.List1

-- Part 1

-- these two functions may or may not be copied from 2024
pairs : Ord a => List a -> List (a,a)
pairs (x :: xs) = map (\i => (x,i)) xs ++ pairs xs
pairs _ = []

neighbors : (Int, Int) -> List (Int, Int)
neighbors j = map ((+) j) (filter (/= (0, 0)) (zip (concat $ replicate 3 [-1, 0, 1]) (concat $ map (replicate 3) [-1, 0, 1])))

rolls : SortedMap (Int, Int) Char -> List (Int, Int)
rolls m = filter ((== (Just '@')) . (flip lookup) m) (keys m)

neighborRolls : SortedMap (Int, Int) Char -> (Int, Int) -> Nat
neighborRolls m pos = length (filter ((== (Just '@')) . (flip lookup) m) (neighbors pos))

partial part1 : Bool -> String -> Int
part1 v input = 
    let m = twoDStringToMap input
        vis = (the (Int -> Int) (trace $ render2DMap (fromList (map (\pos => (pos, ne head (unpack ((the (Nat -> String) cast) (neighborRolls m pos))))) (rolls m)))))
        wrapper: Int -> Int = if v then vis else id in
        wrapper (cast (length (filter (< 4) (map (neighborRolls m) (rolls m)))))

-- Part 2

partial part2 : Bool -> String -> Int
part2 v input = 2

public export
partial solve : Fin 2 -> Bool -> String -> IO Int
solve 0 v = pure . (part1 v)
solve 1 v = pure . (part2 v)