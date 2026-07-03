module Thesis.Poly

import Data.Product
import Data.Coproduct
record Mealy (s, i, o : Type) where
  constructor MkMealy
  return : s -> o
  update : s -> i -> s

MealyLens : Mealy s i o -> MkPoly s (const s) `PolyMap` MkPoly o (const i)
MealyLens (MkMealy r u) = MkPolyMap r u
