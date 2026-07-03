module Data.Some

import Data.Fin
import Data.Sigma
import Data.List

import Data.List.Quantifiers

public export
data Some : (a -> Type) -> List a -> Type where
  Take : {0 p : a -> Type} -> p x -> Some p ls -> Some p (x :: ls)
  Drop : {0 x : a} -> {0 p : a -> Type} -> Some p ls -> Some p (x :: ls)
  Empty : Some p []

public export
zipIndex : {0 a : Type} -> {0 xs : List a} -> {0 p : a -> Type} ->
           Some p xs -> List (Σ (Fin (length xs)) (\i => p (index' xs i)))
zipIndex (Take x y) = (FZ ## x) :: map (\(i ## z) => FS i ## z) (zipIndex y)
zipIndex (Drop x) = map (\(i ## x) => FS i ## x) (zipIndex x)
zipIndex Empty = []

public export
getMissing : {xs : List a} -> Some p xs -> List (Fin (length xs))
getMissing {xs = (x :: ls)} (Take e y) = map FS (getMissing y)
getMissing {xs = (x :: ls)} (Drop xs) = FZ :: map FS (getMissing {xs = ls} xs)
getMissing {xs = []} Empty = []

