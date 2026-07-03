module Data.Container.Sequence.Bifunctor

import Data.Container.Category
import Data.Container.Morphism
import Data.Container.Sequence.Definition

import Data.Category.Bifunctor

public export
(~▷~) :
  {0 a, a', b, b' : Container} ->
  (a =%> a') -> (b =%> b') -> a ▷ b =%> a' ▷ b'
(~▷~) m1 m2 = (<!)
  (\x => MkEx (m1.fwd x.ex1)
              (\y => m2.fwd (x.ex2 (m1.bwd x.ex1 y))))
  (\x, y => (m1.bwd x.ex1 y.π1)
         ## m2.bwd (x.ex2 (m1.bwd x.ex1 y.π1)) y.π2)
public export
SequenceBifunctor : Bifunctor Cont Cont Cont
SequenceBifunctor = MkFunctor
  (Product.uncurry (▷))
  (\_, _, m => m.π1 ~▷~ m.π2)
  (\x => depLensEqToEq $ MkDepLensEq
      (\v2 => exEqToEqRw $ MkExEqRw
          (ExProj1 x.π1 x.π2.req v2) (\_ => Refl))
          (\v, v2 => sigEqToEq $ MkSigEq Refl (IRefl {prf = Refl})))
  (\_, _, _, f, g => Refl)
