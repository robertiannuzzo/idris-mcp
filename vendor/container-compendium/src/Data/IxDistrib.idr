module Data.IxDistrib


import Data.List.Quantifiers
import Data.Maybe.Any

parameters {0 a : Type}

 mayCons : Maybe a -> Maybe (List a) -> Maybe (List a)
 mayCons Nothing xs = Nothing
 mayCons (Just x) (xs) = map (x ::) xs

 distrib : List (Maybe a) -> Maybe (List a)
 distrib [] = Just []
 distrib (x :: xs) = mayCons x (distrib xs)

 parameters {0 p : a -> Type}
  unDist : (xs : List (Maybe a)) -> Any (All p) (distrib xs) -> All (Any p) xs
  unDist [] x = []
  unDist (Nothing :: xs) x = absurd x
  unDist ((Just y) :: xs) x with (distrib xs) proof pq
    unDist ((Just y) :: xs) x | Nothing = absurd x
    unDist ((Just y) :: ys) (Aye (x :: xs)) | (Just z)
      = Aye x :: unDist ys (replace {p = (Any (All p))} (sym pq) (Aye xs))

