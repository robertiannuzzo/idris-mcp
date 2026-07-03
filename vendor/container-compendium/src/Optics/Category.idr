module Optics.Category

import Optics.Lens
import Data.Category
import Data.Boundary
import Data.Coproduct
import Data.Product
import Proofs
||| idLens is the identity when composed to the right
prfidRight : (f : Lens a b) -> (f |> Lens.idLens) ≡ f
prfidRight (MkLens g s) = Refl

||| idLens is the identity when composed to the left
prfIdLeft : (f : Lens a b) -> (Lens.idLens |> f) ≡ f
prfIdLeft (MkLens get set) = Refl

||| composition is associative
prfAssoc : (f : Lens a b) -> (g : Lens b c) -> (h : Lens c d) ->
           (f |> (g |> h)) ≡ ((f |> g) |> h)
prfAssoc {f = (MkLens fget fset)} {g = (MkLens gget gset)} {h = (MkLens hget hset)} = Refl
||| lenses form a category with composition
export
LensCat : Category Boundary
LensCat = MkCategory
  Lens
  (\_ => idLens)
  (|>)
  (\_, _ => prfidRight)
  (\_, _ => prfIdLeft)
  (\_, _, _, _ => prfAssoc)
public export
record Traversal (a, b : Boundary) where
  constructor MkTraversal
  extract : a.π1 -> Σ Nat (\n => Vect n b.π1 * (Vect n b.π2 -> a.π2))
public export
record Affine (a, b : Boundary) where
  constructor MkAffine
  read : a.π1 -> a.π2 + (b.π1 * (b.π2 -> a.π2))
