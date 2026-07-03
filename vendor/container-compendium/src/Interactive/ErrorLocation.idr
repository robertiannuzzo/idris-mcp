module Interactive.ErrorLocation

import Data.Product
import Data.Container
import Data.Container.Morphism
import Data.Container.Maybe.Definition
import Data.Container.List.Functor
import Data.Container.Descriptions.List
import Data.Container.Descriptions.Maybe

import Data.Iso
import Data.List.Quantifiers
import Proofs
data Some : (a -> Type) -> List a -> Type where
  End : {0 a : Type} -> {0 p : a -> Type} ->  Some p []
  Take : {0 a : Type} -> {0 p : a -> Type} -> {0 xs : List a} -> {0 x : a} -> p x -> Some p xs -> Some p (x :: xs)
  Drop : Some p xs -> Some p (x :: xs)
SomeC : Container -> Container
SomeC c = (xs : List c.req) !> Some c.res xs
attempt1 : All.List (Any.Maybe a) =%> SomeC a
attempt1 = ?Problem <! ?attempt1_rhs_1
rebuild1 : (xs : List a) -> All (\x => Maybe (b x)) xs -> Some b xs
rebuild1 [] [] = End
rebuild1 (x :: xs) (Nothing :: z) = Drop (rebuild1 xs z)
rebuild1 (x :: xs) ((Just y) :: z) = Take y (rebuild1 xs z)

rebuild2 : (xs : List a) -> Some b xs -> All (\x => Maybe (b x)) xs
rebuild2 (x :: ls) (Take y z) = Just y :: rebuild2 ls z
rebuild2 (x :: ls) (Drop y) = Nothing :: rebuild2 ls y
rebuild2 [] End = []

rebuildPrf : {0 p : a -> Type} -> (xs : List a) -> (x : All (\x => Maybe (p x)) xs) ->
             rebuild2 xs (rebuild1 xs x) = x
rebuildPrf [] [] = Refl
rebuildPrf (x :: xs) (Nothing :: ys) = cong2 (::) Refl (rebuildPrf xs ys)
rebuildPrf (x :: xs) ((Just y) :: ys) = cong2 (::) Refl (rebuildPrf xs ys)

rebuildPrf2 : {0 p : a -> Type} -> (xs : List a) -> (x : Some (\arg => p arg) xs) -> rebuild1 xs (rebuild2 xs x) = x
rebuildPrf2 [] End = Refl
rebuildPrf2 (y :: xs) (Take x z) = cong (Take x) (rebuildPrf2 xs z)
rebuildPrf2 (y :: xs) (Drop x) = cong Drop (rebuildPrf2 xs x)

SomeAllIso : {xs : _} -> Some p xs ≅ Quantifiers.All.All (Maybe . p) xs
SomeAllIso = MkIso
    (rebuild2 xs)
    (rebuild1 xs)
    (rebuildPrf xs)
    (rebuildPrf2 xs)
allToSome : All.List ((x : a) !> Maybe (b x)) =%> SomeC ((!>) a b)
allToSome = id <! rebuild2

someToAll : SomeC ((!>) a b) =%> All.List ((x : a) !> Maybe (b x))
someToAll = id <! rebuild1
