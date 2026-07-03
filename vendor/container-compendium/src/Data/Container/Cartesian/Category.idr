module Data.Container.Cartesian.Category

import Data.Category
import Data.Category.NaturalTransformation
import Data.Category.Monoid
import Data.Category.Functor

import Data.Container.Definition
import Data.Container.Cartesian
import Data.Container.Category
import Data.Container.Morphism.Definition
import Data.Iso

import Data.Product

import Proofs

%hide Prelude.Ops.infixl.(|>)
--------------------------------------------------------------------------------
-- Cartesian lenses form a category
--------------------------------------------------------------------------------
0 identityLeft :
    (a, b : Container) -> (f : a =#> b) ->
    Cartesian.identity a |#> f ≡#>≡ f
identityLeft a b (MkCartDepLens fwd bwd) = MkCartDepLensEq
    (\_ => Refl)
    (\f => isoIdRight (bwd f))
0 identityRight :
    (a, b : Container) -> (f : a =#> b) ->
    f |#> Cartesian.identity b ≡#>≡ f
identityRight a b (MkCartDepLens f1 bwd) = MkCartDepLensEq (\_ => Refl)
    (\f => isoIdLeft (bwd f))
0 proofComposition :
    (f : a =#> b) -> (g : b =#> c) -> (h : c =#> d) ->
    f |#> (g |#> h) ≡#>≡ (f |#> g) |#> h
proofComposition
  (MkCartDepLens fwd1 bwd1) (MkCartDepLens fwd2 bwd2) (MkCartDepLens fwd3 bwd3) =
  MkCartDepLensEq (\_ => Refl) (\f =>
    symIsoEq $ transIsoAssoc (bwd3 (fwd2 (fwd1 f))) (bwd2 (fwd1 f)) (bwd1 f)
    )
||| Cartesian containers category, where objects are containers and morphisms are cartesian lense
public export
ContCart : Category Container
ContCart = MkCategory
  (\a, b => a =#> b)
  (\_ => identity _)
  Cartesian.(|#>)
  (\_, _, f => cartEqToEq (identityRight _ _ f))
  (\_, _, f => cartEqToEq (identityLeft _ _ f))
  (\_, _, _, _, f, g, h => cartEqToEq (proofComposition f g h))
public export
toLens : (0 a, b : Container) -> a =#> b -> a =%> b
toLens a b x = x.cfwd <! (\y => to (x.cbwd y))
CartToCont : ContCart ->> Cont
CartToCont = MkFunctor
    { mapObj = Basics.id
    , mapHom = (\x, y => toLens x y)
    , presId = (\_ => Refl)
    , presComp = (\x, y, z, f, g => Refl)
    }
