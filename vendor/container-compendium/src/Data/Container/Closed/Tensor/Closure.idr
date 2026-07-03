module Data.Container.Closed.Tensor.Closure

import Data.Container
import Data.Container.Closed
private infixr 1 ⇒
(⇒) : Container -> Container -> Container
(⇒) a b = (m : a =&> b) !> Σ (i : a.request) | b.response (π1 (m.fn i))

curry : a ⊗ b =&> c -> a =&> b ⇒ c
curry (!! xm) =
    !! \x => (!! \y => let gg = xm (x && y) in gg.π1 ## (π2 . gg.π2))
    ## (\z => let qq = (xm (x && z.π1)).π2 z.π2 in qq.π1)
