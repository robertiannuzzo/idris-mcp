module Data.Container.Closed.Tensor.Monoidal

import Data.Container.Closed
import Data.Container.Closed.Category
import Data.Container.Closed.Tensor.Bifunctor
import Data.Container.Definition
import Data.Container.Tensor.Definition

import Data.Category.Monoid
import Data.Category.Product
public export
unitL : I ⊗ a =&> a
unitL = !! \x => x.π2 ## (() &&)

public export
unitR : a ⊗ I =&> a
unitR = !! \x => x.π1 ## (&& ())

alpha : let f1, f2 : (Cont × (Cont × Cont)) ->> Cont
            f1 = ((idF Cont) `pair` TensorBifunctor) ⨾⨾ TensorBifunctor
            f2 = assocR {a = Cont, b = Cont, c = Cont}
                ⨾⨾ ((TensorBifunctor `pair` idF Cont) ⨾⨾ TensorBifunctor)
        in f1 =~= f2

public export
TensorMonoidal : Monoidal Cont
TensorMonoidal = MkMonoidal
  TensorBifunctor
  I
  alpha
  ?ddd
  ?eee
