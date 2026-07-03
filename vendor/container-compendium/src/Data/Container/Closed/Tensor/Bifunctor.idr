module Data.Container.Closed.Tensor.Bifunctor

import Data.Container.Closed
import Data.Container.Closed.Category
import Data.Container.Closed.Eq
import Data.Container.Tensor.Definition
import Data.Container.Tensor.Bifunctor

import Data.Category.Bifunctor

public export
swap : (a ⊗ b) =&> (a ⊗ b)
-- swap = !! \x => swap {a = a.req, b = b.req} x ## ?aa

public export
(~⊗~) : a =&> b -> a' =&> b' -> a ⊗ a' =&> b ⊗ b'
(~⊗~) m n = !! \x => let y1 = m.fn x.π1 ; y2 = n.fn x.π2 in (y1.π1 && y2.π1) ## bimap y1.π2 y2.π2

public export
TensorBifunctor : Bifunctor Cont Cont Cont
TensorBifunctor = MkFunctor
    (uncurry (⊗))
    (\_, _, m => m.π1 ~⊗~ m.π2)
    (\_ => clsEqToEq SigEq' sigEqToEq' $ MkClsEq $ \(x && y) =>
            MkSigEq' ?bdb ?presId)
    (\x, y, z, f, g => ?presCopm)

