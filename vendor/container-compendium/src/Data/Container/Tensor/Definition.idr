module Data.Container.Tensor.Definition

import Data.Container.Definition
import public Data.Product
public export
(⊗) : (c1, c2 : Container) -> Container
(⊗) c1 c2 = (x : c1.req * c2.req) !> c1.res x.π1 * c2.res x.π2
