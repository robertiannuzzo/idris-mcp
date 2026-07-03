module Data.Category.Initial

import Data.Category

public export
record HasInitial {0 o : Type} (cat : Category o) where
  constructor MkInitial

  -- The initial object
  initial : o

  -- Each object has a morphism from the initial object
  unit : (v : o) -> initial ~> v

  -- Each morphism from the initial object is unique
  toInitUniq : (v : o) -> (m : initial ~> v) -> m = unit v
