module Data.Product

import public Data.Ops
import Data.Vect

%default total
%hide Prelude.(&&)
%hide Prelude.Num.(*)

||| Pairs of types
public export
record (*) (a, b : Type) where
  constructor (&&)
  π1 : a
  π2 : b
%pair (*) π1 π2
public export
Show a => Show b => Show (a * b) where
  show (a && b) = "\{show a} & \{show b}"

||| Swap the two elements of a product
public export
swap : a * b -> b * a
swap x = x.π2 && x.π1

||| Convert from a product to a pair
public export
toPair : a * b -> (a, b)
toPair x = (x.π1, x.π2)

||| Convert from a pair to a product
public export
fromPair : (a, b) -> (a * b)
fromPair x = fst x && snd x

public export
Bifunctor (*) where
  bimap f g x = f x.π1 && g x.π2
||| Duplicate an element
public export
dup : a -> a * a
dup x = x && x

public export
distribute : a * b -> c * d -> (a * c) * (b * d)
distribute x y = (x.π1 && y.π1) && (x.π2 && y.π2)

export
fork : (a -> b) -> (a -> c) -> a -> b * c
fork f g x = f x && g x

export
split : (a * b) * c -> (a * c) * (b * c)
split ((a && b) && c) = (a && c) && (b && c)

||| Like bimap but with two arguments
export
through : (a -> b -> c) -> (x -> y -> z) -> (a * x) -> (b * y) -> (c * z)
through f g x y = f x.π1 y.π1 && g x.π2 y.π2

||| From arity 2 to arity 1 with pair
public export
curry : (a * b -> c) -> a -> b -> c
curry f a b = f (a && b)
public export
shuffle : (a * x) * (b * y) -> (a * b) * (x * y)
shuffle ((a && x) && (b && y)) = (a && b) && (x && y)

||| From arity 2 to arity 1 with pair
public export
uncurry : (a -> b -> c) -> a * b -> c
uncurry f x = f x.π1 x.π2
public export
assocL : (a * b) * c -> a * (b * c)
assocL x = x.π1.π1 && (x.π1.π2 && x.π2)
public export
assocR : a * (b * c) -> (a * b) * c
assocR x = (x.π1 && x.π2.π1) && x.π2.π2
public export
proj1Pair : (0 a, b : _) -> (a && b).π1 === a
proj1Pair _ _ = Refl
public export
proj2Pair : (0 a, b : _) -> (a && b).π2 === b
proj2Pair _ _ = Refl
public export
projIdentity : (x : a * b) -> (x.π1 && x.π2) === x
projIdentity (a && b) = Refl
public export
pairUniq : (x : a * b) -> (x.π1 && x.π2) === x
pairUniq (a && b) = Refl
