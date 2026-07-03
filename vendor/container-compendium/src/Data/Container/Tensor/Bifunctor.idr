module Data.Container.Tensor.Bifunctor

import Data.Category
import Data.Category.Functor
import Data.Category.Bifunctor

import Data.Container.Category
import Data.Container.Definition
import Data.Container.Morphism.Definition
import Data.Container.Tensor.Definition

public export
(~⊗~) : (a =%> b) -> (a' =%> b') -> a ⊗ a' =%> b ⊗ b'
(~⊗~) x y = (bimap x.fwd y.fwd) <! (\v, w => x.bwd v.π1 w.π1 && y.bwd v.π2 w.π2)
public export
parallel : (a =%> b) -> (a' =%> b') -> a ⊗ a' =%> b ⊗ b'
parallel = (~⊗~)
public export
TensorBifunctor : Bifunctor Cont Cont Cont
TensorBifunctor = MkFunctor
    (uncurry (⊗))
    (\x, y, m => m.π1 ~⊗~ m.π2)
    (\v => depLensEqToEq $ MkDepLensEq
        (\vx => prodUniq vx)
        (\vx, vy => prodUniq vy)
    )
    (\a, b, c, f, g => Refl)
