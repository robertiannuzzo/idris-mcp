module Data.Category.Set.Product

import Data.Category
import Data.Category.Product

import Proofs.Product

SetHasProducts : HasProduct Set
SetHasProducts = MkProd
    (*)
    (π1)
    (π2)
    (\f, g, x => f x && g x)
    (\f, g => Refl)
    (\f, g => Refl)
    (\Refl, Refl => funExt $ \x => prodUniq _)

