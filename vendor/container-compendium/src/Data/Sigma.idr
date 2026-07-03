module Data.Sigma

import Data.Ops

import Proofs.Equality

public export
typebind
record Σ (a : Type) (b : a -> Type) where
  constructor (##)
  ||| First projection of sigma
  π1 : a
  ||| Second projection of sigma
  π2 : b π1
%name (##) p1, p2
%pair Σ π1 π2
Product : Type -> Type -> Type
Product a b = Σ (_ : a) | b
Coproduct : Type -> Type -> Type
Coproduct a b = Σ (isLeft : Bool) | if isLeft then a else b
public export
elimSig : {0 a : Type} -> {0 b : a -> Type} ->
          {0 d : Σ a b -> Type} ->
          (s : Σ a b) -> ((x : a) -> (y : b x) -> (p : x === s.π1) -> (y ≡≡ s.π2) {p = b} -> d (x ## y)) -> d s
elimSig (p1 ## p2) f = f p1 p2 Refl (IRefl Refl)

export
Uninhabited a => Uninhabited (Σ a b) where
  uninhabited x = absurd x.π1
