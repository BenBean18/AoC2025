module Day10

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

-- This is simply finding the pseudoinverse of a matrix in the finite field containing only 0 and 1
-- Time to implement row reduction I guess
-- It'll be good review and fun hopefully, also linalg over finite fields is interesting

-- define a zero
data ZeroExists: t -> Type where
    IsZero: {auto n: Num t} -> {auto e: Eq t} -> {z: t} -> {auto p: (right: t) -> z + right = right} -> ZeroExists t

interface (e: Eq t) => (n: Num t) => HasZero t where
    ZeroProof: ZeroExists t

HasZero Nat where
    ZeroProof = IsZero {z=0} {p=plusZeroLeftNeutral}

finZeroLeftNeutral: (right: Fin (S n)) -> FZ + right = right
finZeroLeftNeutral 0 = Refl
finZeroLeftNeutral (FS k) = Refl

finZeroRightNeutral: {n: Nat} -> (left: Fin (S n)) -> left + FZ = left
finZeroRightNeutral 0 = Refl
finZeroRightNeutral left = believe_me (left + FZ = left) True

(n: Nat) => HasZero (Fin (S n)) where
    ZeroProof = IsZero {z=FZ} {p=finZeroLeftNeutral}

extractZero: ZeroExists t -> t
extractZero (IsZero {z=z}) = z

zero: HasZero t => t
zero = extractZero ZeroProof

-- define a one
data OneExists: t -> Type where
    IsOne: {auto n: Num t} -> {auto e: Eq t} -> {o: t} -> {auto p: (right: t) -> o * right = right} -> OneExists t

interface (e: Eq t) => (n: Num t) => HasOne t where
    OneProof: OneExists t

HasOne Nat where
    OneProof = IsOne {o=1} {p=multOneLeftNeutral}

weakenedZeroIsZero: weaken FZ = FZ
weakenedZeroIsZero = Refl

assertSmallerZeroZeroIsZero: assert_smaller Data.Fin.FZ (weaken FZ) = FZ
assertSmallerZeroZeroIsZero = Refl

finOneLeftNeutral: {n: Nat} -> (right: Fin (S (S n))) -> (FS FZ) * right = right
finOneLeftNeutral k = finZeroRightNeutral k

(n: Nat) => HasOne (Fin (S (S n))) where
    OneProof = IsOne {o=1} {p=finOneLeftNeutral}

extractOne: OneExists t -> t
extractOne (IsOne {o=o}) = o

one: HasOne t => t
one = extractOne OneProof

interface HasZero t => HasOne t => Num t => Ring t where

interface Ring t => Neg t => Integral t => Field t where

-- Field Nat where
--     Zero (IsZero Nat z) = 0
--     One = 1

Integral (Fin 2) where  
    mod x 1 = x

    div x 1 = x

Ring (Fin 2) where

Field (Fin 2) where

HasZero Double where
    ZeroProof = IsZero {z=0} {p= \right => believe_me (0 + right = right) True}

HasOne Double where
    OneProof = IsOne {o=1} {p= \right => believe_me (1 * right = right) True}

Ring Double where

Integral Double where
    div a b = a / b

    mod a b = ?no_mod_for_double_womp_womp

Field Double where

-- data Field : t -> Type where
--    Zero: Num' t => {a: t} -> {p: IsZero a} -> Field t
--    One: {p: a * t = a} -> Field @{e} @{n} t

-- isZero: Field t => (a: t) -> (the t Zero) + a = t
-- isZero t = Refl

(n: Nat) => Num t => Num (Vect n t) where   
    fromInteger i = replicate n (fromInteger i)

    (*) = zipWith (*)

    (+) = zipWith (+)

sm: Num t => t -> Vect n t -> Vect n t
sm s [] = []
sm s (x::xs) = x*s :: sm s xs

{-


[2] 2
 4  3

2 is our pivot.
r2 -= (4/2) * r1

[2] 2
 0  -1

Column is clear, move to next pivot

 2  2
 0 [-1]

r1 -= (2/-1) * r2

 2  0
 0 [-1]

All pivots are cleared, normalize rows

 -}

-- we'll store a matrix row-wise, it'll be more useful here I think
0 Matrix: Nat -> Nat -> Type -> Type
Matrix m n t = Vect m (Vect n t) -- m rows, n cols

mm: Num t => {k: Nat} -> {m: Nat} -> {n: Nat} -> Matrix k m t -> Matrix m n t -> Matrix k n t
mm a b = map (\rowA => sum $ map (\(coeff, rowB) => coeff `sm` rowB) (zip rowA b)) a -- rows combine rows to the right

enumerate: {n: Nat} -> Vect n t -> Vect n (Fin n, t)
enumerate l = zip (allFins n) l

eliminateAboveAndBelow: Field t => {m: Nat} -> {n: Nat} -> Matrix m n t -> (Fin m) -> (Fin n) -> Matrix m n t
eliminateAboveAndBelow a r c =
    let pivot = index c (index r a)
        multiplesToSubtractOfRow = map (\(idx, row) => if idx == r then (the t zero) else (index c row) `div` pivot) (enumerate a)
        pivotRow = index r a in map (\(multiple, row) => row + (replicate n (-multiple)) * pivotRow) (zip multiplesToSubtractOfRow a)

scaleToOne: Field t => {n: Nat} -> Vect n t -> Vect n t
scaleToOne xs = case (filter (/= (the t zero)) (toList xs)) of
    [] => xs -- all zero
    (firstNonzero :: _) => (replicate n ((the t one) `div` firstNonzero)) * xs

isColumnZero: Eq t => Field t => {m: Nat} -> {n: Nat} -> Fin n -> Matrix m n t -> Bool
isColumnZero c m = let col = map (index c) m in 0 == (length (filter (/= (the t zero)) (toList col)))

rowReduce': Eq t => Field t => {m: Nat} -> {n: Nat} -> Matrix (S m) (S n) t -> Fin (S m) -> Fin (S n) -> Matrix (S m) (S n) t
rowReduce' [a] r c = [scaleToOne a]
rowReduce' (x :: xs) r c =
    let pivot = index c (index r (x :: xs)) in
        if isColumnZero c (x :: xs) then rowReduce' (eliminateAboveAndBelow (x :: xs) r c) r (finS c)
        else if pivot == (the t zero) then rowReduce' (reverse (x :: reverse xs)) r c
        else if r == (the (Fin (S m)) last) then (eliminateAboveAndBelow (x :: xs) r c)
        else rowReduce' (eliminateAboveAndBelow (x :: xs) r c) (finS r) (finS c)

rref: Eq t => Field t => {m: Nat} -> {n: Nat} -> Matrix (S m) (S n) t -> Matrix (S m) (S n) t
rref a = map scaleToOne (rowReduce' a 0 0)

onehot: HasZero t => HasOne t => {n: Nat} -> Fin n -> Vect n t
onehot k = map (\i => if i == k then (the t one) else (the t zero)) (allFins n)

eye: Eq t => Field t => (n: Nat) -> Matrix n n t
eye n = map onehot (allFins n)

augment: Matrix m j t -> Matrix m k t -> Matrix m (j + k) t
augment a b = zipWith (++) a b

takeNCols: (k: Nat) -> Matrix m (k + n) t -> Matrix m k t
takeNCols k m = map (take k) m

dropNCols: (k: Nat) -> Matrix m (k + n) t -> Matrix m n t
dropNCols k m = map (drop k) m

inv: Eq t => Field t => {n: Nat} -> Matrix (S n) (S n) t -> Matrix (S n) (S n) t
inv m = dropNCols (S n) (rref (augment m (eye (S n))))

-- we have linearly independent rows (most likely, assuming no dups) so we use A.T @ (A A.T)^{-1}
linv: Eq t => Field t => {m: Nat} -> {n: Nat} -> Matrix (S m) (S n) t -> Matrix (S n) (S m) t
linv m = (inv ((transpose m) `mm` m)) `mm` (transpose m)

rinv: Eq t => Field t => {m: Nat} -> {n: Nat} -> Matrix (S m) (S n) t -> Matrix (S n) (S m) t
rinv m = (transpose m) `mm` (inv (m `mm` (transpose m)))

A: Matrix 4 6 (Fin 2)
A = transpose [[0,0,0,1],[0,1,0,1],[0,0,1,0],[0,0,1,1],[1,0,1,0],[1,1,0,0]]

b: Matrix 4 1 (Fin 2)
b = transpose [[0,1,1,0]]

A_test: Matrix 3 3 Double
A_test = [[0,1,1],[1,0,3],[4,5,0]]

O: Fin 2
O = 1

Z: Fin 2
Z = 0

-- row exchanges make it so that we don't know the right combination of buttons to press (they've been reordered)
-- but we still know the correct number so we're fine!

buildVectFromText': String -> {n: Nat} -> Vect (S n) (Fin 2)
buildVectFromText' s = sum (map (\w => onehot (the (Fin (S n)) (restrict n (cast w)))) (split (== ',') s))

buildVectFromText: {n: Nat} -> String -> Vect (S n) (Fin 2)
buildVectFromText s = buildVectFromText' (pack (ne tail (ne init (unpack s))))

-- [.##.] (3) (1,3) (2) (2,3) (0,2) (0,1) {3,5,4,7}
buildGoalFromText: Vect (S (S n)) Char -> Vect n (Fin 2)
buildGoalFromText s = map (\c => if c == '#' then FS FZ else FZ) (tail (init s))

magicLength: String -> Nat
magicLength s = cast (natToInteger (length (ne Data.List.head (words s))) - cast 2)

vectsForString: String -> Nat
vectsForString s = cast (natToInteger (length (words s)) - cast 2)

partial parseLine: (s: String) -> (Vect (S (magicLength s)) (Fin 2), Vect (vectsForString s) (Vect (S (magicLength s)) (Fin 2)))
parseLine s =
    let (goal :: vects) = ne init (words s)
        n = length (ne Data.List.head (words s)) in (
            reverse (FZ :: reverse (buildGoalFromText (fromJust @{believe_me (IsJust ((toVect (S (S (magicLength s))) (unpack goal))))} (toVect (S (S (magicLength s))) (unpack goal))))),
            fromJust @{believe_me (IsJust (toVect (vectsForString s) (map (buildVectFromText {n=magicLength s}) vects)))} (toVect (vectsForString s) (map (buildVectFromText {n=magicLength s}) vects)))

solveLine: {n: Nat} -> {k: Nat} -> (Vect (S (S n)) (Fin 2), Vect (S k) (Vect (S (S n)) (Fin 2))) -> Nat
solveLine (goal, vects) =
    let matrix: Matrix (S n) (S k) (Fin 2) = transpose (map init vects)
        trimmedGoal: Vect (S n) (Fin 2) = init goal
        soln: Matrix (S k) 1 (Fin 2) = ((rinv matrix) `mm` (transpose [trimmedGoal]))
        tSoln: Matrix 1 (S k) (Fin 2) = transpose soln
        flattened: Vect (S k) (Fin 2) = head tSoln in length (filter (== FS FZ) (toList flattened))

result: (Vect 5 (Fin 2), Vect 6 (Vect 5 (Fin 2)))
result = ([0, 1, 1, 0, 0], [[0, 0, 0, 1, 0], [0, 1, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [1, 0, 1, 0, 0], [1, 1, 0, 0, 0]])

partial test: IO ()
test = print (solveLine (parseLine "[.##.] (3) (1,3) (2) (2,3) (0,2) (0,1) {3,5,4,7}"))

vectorIsNowAtLeastTwo: {k: Nat} -> Vect n t -> Vect (S (S k)) t
vectorIsNowAtLeastTwo v = fromJust @{believe_me (IsJust (toVect (S (S k)) (toList v)))} (toVect (S (S k)) (toList v))

partial processLine: String -> Nat
processLine s =
    let (goal', vects') = parseLine s
        goal = vectorIsNowAtLeastTwo {k=cast (natToInteger (length goal') - 2)} goal'
        vects = vectorIsNowAtLeastTwo {k=cast (natToInteger (length vects') - 2)} $ map (vectorIsNowAtLeastTwo {k=cast (natToInteger (length goal') - 2)}) vects' in solveLine (goal, vects)

partial part1 : String -> Int
part1 input = (trace $ show (map processLine (lines input))) $ cast $ sum $ map processLine (lines input)

-- Part 2

partial part2 : String -> Int
part2 input = 2

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2