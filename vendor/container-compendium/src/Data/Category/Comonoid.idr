module Data.Category.Comonoid

import Data.Category
import Data.Category.Bifunctor

record Comonoidal {0 o : Type} (c : Category o) where
  constructor MkMonoidal

  comult : Functor c (c * c)

  erase : Functor c UnitCat

 -- todo: add the laws
record ComonoidObject {0 o : Type} {cat : Category o} (mon : Comonoidal cat) where
  constructor MkMonObj
  obj : o
  η : obj ~> counit
  μ : obj ⊗ obj ~> obj
