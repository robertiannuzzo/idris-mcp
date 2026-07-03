module Data.Container.Morphism

import public Data.Container.Definition
import public Data.Container.Tensor.Definition
import public Data.Container.Sequence.Definition
import public Data.Container.Extension
import public Data.Container.Morphism.Definition
import public Data.Container.Morphism.Context
import public Data.Container.Morphism.Eq
import public Data.Ops
import public Data.Category.Ops
import Data.Coproduct
import Data.Product
import Data.Alg
import Data.Sigma

import Control.Order
import Control.Relation
-- ▷ distributes over ⊗
public export
distribProd : (a1 ▷ a2) ⊗ (b1 ▷ b2) =%> (a1 ⊗ b1) ▷ (a2 ⊗ b2)
distribProd =
    (\x => MkEx (x.π1.ex1 && x.π2.ex1) (\vx => x.π1.ex2 vx.π1 && x.π2.ex2 vx.π2 )) <!
    (\x, y => y.π1.π1 ## y.π2.π1 && y.π1.π2 ## y.π2.π2)
