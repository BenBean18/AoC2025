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

partial part1 : String -> Int
part1 input = 1

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

A: Matrix 4 2 Double
A = [[0.16430899, 0.70363687], [0.83788205, 0.85589945], [0.23122045, 0.69569817], [0.12175106, 0.97940617]]

B: Matrix 2 3 Double
B = [[0.45950091, 0.48214121, 0.35390089], [0.75577587, 0.18892848, 0.71213365]]

C: Matrix 2 2 Double
C = [[2,2],[4,3]]

D: Matrix 3 6 Double
D = [[1,2,3,1,0,0],[4,5,6,0,1,0],[7,10,9,0,0,1]]

E: Matrix 3 3 Double
E = [[1,2,3],[4,5,6],[7,10,9]]

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

rowReduce': Eq t => Field t => {m: Nat} -> {n: Nat} -> Matrix (S m) (S n) t -> Fin (S m) -> Fin (S n) -> Matrix (S m) (S n) t
rowReduce' [a] r c = [scaleToOne a]
rowReduce' (x :: xs) r c =
    let pivot = index c (index r (x :: xs)) in
        if pivot == (the t zero) then rowReduce' (reverse (x :: reverse xs)) r c
        else if r == (the (Fin (S m)) last) then (eliminateAboveAndBelow (x :: xs) r c)
        else rowReduce' (eliminateAboveAndBelow (x :: xs) r c) (finS r) (finS c)

rref: Eq t => Field t => {m: Nat} -> {n: Nat} -> Matrix (S m) (S n) t -> Matrix (S m) (S n) t
rref a = map scaleToOne (rowReduce' a 0 0)

-- Part 2

partial part2 : String -> Int
part2 input = 2

public export
partial solve : Fin 2 -> String -> IO Int
solve 0 = pure . part1
solve 1 = pure . part2