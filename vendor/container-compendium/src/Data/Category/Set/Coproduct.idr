module Data.Category.Set.Coproduct

import Data.Category
import Data.Category.Product

import Data.Coproduct
import Proofs.Product

SetHasCoproducts : HasProduct (Set .op)
SetHasCoproducts = MkProd
    (+)
    (<+)
    (+>)
    choice
    (\f, g => Refl)
    (\f, g => Refl)
    (\p, q => funExt $ \case (<+ x) => rewrite sym p in Refl
                             (+> x) => rewrite sym q in Refl)

