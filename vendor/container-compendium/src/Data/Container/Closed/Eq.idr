module Data.Container.Closed.Eq

import Data.Container.Definition
import Data.Container.Closed.Definition
import Data.Container.Morphism.Definition
import Data.Container.Morphism.Eq

import Data.Sigma

import Proofs

public export
record ClosedEq (l1, l2 : a =&> b)
                (eq : {base : Type} -> {fibre : base -> Type} ->
                      (_, _ : Σ base fibre) -> Type) where
  constructor MkClsEq
  clsEq : (x : a.req) -> (l1.fn x) `eq` (l2.fn x)

export 0
clsEqToEq : (f : {base : Type} -> {fibre : base -> Type} ->
                      (_, _ : Σ base fibre) -> Type) ->
            (fToEq : {a : Type} -> {b : a -> Type} ->
                     {x, y : Σ a b} -> f x y -> x === y) ->
            ClosedEq l1 l2 f -> l1 ≡ l2
clsEqToEq {l1 = !! l1} {l2 = !! l2} f fToEq (MkClsEq clsEq) =
  cong (!!) (funExtDep $ \x => fToEq (clsEq x))

export
reflEq : {m : a =&> b} ->
         {0 f : {base : Type} -> {fibre : base -> Type} ->
              (_, _ : Σ base fibre) -> Type} ->
         (refl : {0 base : Type} -> {0 fibre : base -> Type} ->
                 (x : Σ base fibre) -> f x x) ->
         ClosedEq m m f
reflEq refl = MkClsEq $ \xx => refl (m.fn xx)

