module Data.Container.Closed.Tensor

import Data.Container.Closed
import Data.Container.Closed.Maybe.Functor
import Data.Container.Tensor.Definition
import Data.Container.Tensor.Bifunctor

import Data.Container.Maybe

import Data.Product
import Data.Maybe.Any
import Data.Maybe.All
namespace Any
  export
  strengthL : Any.Maybe a ⊗ b =&> Any.Maybe (a ⊗ b)
  strengthL = !! \case (Nothing && p2) => Nothing ## absurd
                       ((Just x) && p2) => Just (x && p2) ## \(Aye y) => Aye y.π1 && y.π2

  export
  strengthR : a ⊗ Any.Maybe b =&> Any.Maybe (a ⊗ b)
  strengthR = !! \case (p1 && Nothing) => Nothing ## absurd
                       (p1 && (Just x)) => Just (p1 && x) ## \(Aye y) => y.π1 && Aye y.π2


-- there is no strength for All.Maybe
namespace All
 failing
  export
  strength : All.Maybe a ⊗ b =&> All.Maybe (a ⊗ b)
  strength = !! \case (Nothing && p2) => Nothing ## \case (Nay) => Nay && ()
                      ((Just x) && p2) => ?strengthL_rhs_2
