module Data.Container.Monadic
import Data.Container.Definition
import Data.Category.NaturalTransformation
import Data.Category.Bifunctor
import Data.Category.Functor
import Data.Category.FunctorCat
import Data.Category.Endofunctor
import Data.Container.Category

import Proofs

private infixl 1 $-
($-) : (Type -> Type) -> Container -> Container
($-) f c = (x : c.req) !> f (c.res x)
fApplyBifunctor : Bifunctor (EndoCat Set).op Cont Cont
fApplyBifunctor = MkFunctor
    (\f => f.π1.mapObj $- f.π2)
    mapHom
    presId
    presComp
    where
      mapHom : (x, y : Endo Set * Container) ->
               (y.π1 =>> x.π1) * (x.π2 =%> y.π2) ->
               x.π1.mapObj $- x.π2 =%> y.π1.mapObj $- y.π2
      mapHom x y (nt && mor) = mor.fwd <! \z, w =>
                               let fy : (y .π1) .mapObj ((x .π2) .response z)
                                 ; fy = y.π1.mapHom ? ? (mor.bwd z) w
                                in nt.component (x.π2.res z) fy
      0 presId : (v : Endo Set * Container) ->
               mapHom v v (((EndoCat Set) .op * Cont).id v)
               === Cont .id (v.π1.mapObj $- v.π2)
      presId ((MkFunctor mo mh pid pcp) && p2) = depLensEqToEq $ MkDepLensEq
          (\_ => Refl)
          (\v, z => let 0 prf = app ? ? (pid (p2 .response v)) z
              in trans (cong (mh (p2 .response v) (p2 .response v) id) prf) prf)
      0 presComp :
        (x, y, z : Endo Set * Container) -> -- given three objects x, y, z
        (f : (y.π1 =>> x.π1) * (x.π2 =%> y.π2)) ->   -- a morphism x -> y
        (g : (z.π1 =>> y.π1) * (y.π2 =%> z.π2)) ->   -- and a morphism y -> z

        let 0 f1, f2 : (x.π1.mapObj $- x.π2) =%> (z.π1.mapObj $- z.π2)
            -- Mapping the morphism after composition
            f1 = mapHom x z (g.π1 ⨾⨾⨾ f.π1 && (f.π2 |%> g.π2))
            -- -- And composing the maps of each morphism
            f2 = mapHom x y f |%> mapHom y z g
        in f1 === f2 -- Are the same thing
      presComp x y z f g = depLensEqToEq $ MkDepLensEq
          (\w => let xf = x.π1.presComp ? ? ? f.π2.fwd
                     yf = y.π1.presComp
                     zf = z.π1.presComp
                     ff = f.π1.commutes
                     gf = g.π1.commutes
                  in ?presComp_rhs)
          ?presComp_rhs2
