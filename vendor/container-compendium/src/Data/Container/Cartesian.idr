module Data.Container.Cartesian

import Data.Container.Category
import Data.Container.Extension.Definition
import Data.Container.Definition

import Data.Coproduct
import Data.Iso
import Data.Sigma

import Control.Relation

import Proofs

%default total

||| Cartesian dependent lenses. Their forward part is the same as a dependent lens
||| But their backward part is an isomorphism.
public export
record (=#>) (0 a, b : Container) where
  constructor MkCartDepLens
  -- `c` for cartesian forward map
  cfwd : a.req -> b.req
  -- `c` for cartesian backward map
  cbwd : (x : a.req) -> b.res (cfwd x) ≅ a.res x
infix 5 <#!
public export
(<#!) : {0 a, b : Container} ->
    (fwd : a.req -> b.req) -> (bwd : (x : a.req) -> b.res (fwd x) ≅ a.res x) ->
    a =#> b
(<#!) = MkCartDepLens
public export
record CartDepLensEq (a, b : dom =#> cod) where
  constructor MkCartDepLensEq
  fwdEq : (x : dom.req) -> a.cfwd x === b.cfwd x
  bwdEq : (x : dom.req) ->
          let 0 p1 : cod.res (a.cfwd x) ≅ dom.res x
              p1 = a.cbwd x
              0 p2 : cod.res (a.cfwd x) ≅ dom.res x
              p2 = replace
                     {p = \arg => cod.res arg ≅ dom.res x}
                     (sym $ fwdEq x)
                     (b.cbwd x)
          in IsoEq p1 p2

export infix 0 ≡#>≡

public export
(≡#>≡) : (a, b : dom =#> cod) -> Type
(≡#>≡) = CartDepLensEq

export
0 cartEqToEq : CartDepLensEq a b -> a === b
cartEqToEq {a = (MkCartDepLens fwd1 bwd1)} {b = (MkCartDepLens fwd2 bwd2)} (MkCartDepLensEq fwdEq bwdEq) =
  cong2Dep' MkCartDepLens (funExt fwdEq) (funExtDep $ \x => fromIsoEq _ _ (bwdEq x))
public export
(|#>) : {0 a, b, c : Container} -> a =#> b -> b =#> c -> a =#> c
(|#>) m1 m2 =
  let f1 : a.req -> b.req
      f1 = m1.cfwd
      b1 : (x : a.req) -> b.res (f1 x) ≅ a.res x
      b1 = m1.cbwd
      f2 : b.req -> c.req
      f2 = m2.cfwd
      b2 : (x : b.req) -> c.res (f2 x) ≅ b.res x
      b2 = m2.cbwd
  in MkCartDepLens (f2 . f1)
    (\x => transIso (b2 (f1 x)) (b1 x))
public export
identity : (0 v : Container) -> v =#> v
identity v = MkCartDepLens id (\x => Iso.identity (v.res x))
export
cartFwdEq : (f : a =#> b) -> (g : b =#> c) -> (x : Ex a a'.req) ->
        (f |#> g) .cfwd (x .ex1) = g .cfwd (f .cfwd (x .ex1))
cartFwdEq f g x = Refl

export
cartBwdEq : (f : a =#> b) -> (g : b =#> c) -> (x : Ex a a'.req) ->
        (y : c .res ((f |#> g) .cfwd (x .ex1))) ->
        ((f |#> g).cbwd (x .ex1)).to y === (f.cbwd x.ex1).to ((g.cbwd (f.cfwd x.ex1)).to y)
cartBwdEq f g x y = Refl
public export
record CartDepLensEqTr (a, b : dom =#> cod) where
  constructor MkCartDepLensEqTr
  fwdEq : (x : dom.req) -> a.cfwd x === b.cfwd x
  bwdEq : (x : dom.req) ->
          let 0 p1 : cod.res (a.cfwd x) ≅ dom.res x
              p1 = a.cbwd x
              0 p2 : cod.res (a.cfwd x) ≅ dom.res x
              p2 = transport (\arg => cod.res arg ≅ dom.res x) (sym $ fwdEq x) (b.cbwd x)
          in IsoEq p1 p2

export
0 cartEqToEqTr : {0 a, b : dom =#> cod} -> CartDepLensEqTr a b -> a === b
cartEqToEqTr {a = (MkCartDepLens fwd1 bwd1)} {b = (MkCartDepLens fwd2 bwd2)} (MkCartDepLensEqTr fwdEq bwdEq) =
  cong2Dep' MkCartDepLens (funExt fwdEq) (funExtDep $ \x => let gg = fromIsoEq _ _ (bwdEq x)
      in trans gg (applyTransport (\arg => cod.response arg ≅ dom.response x) (bwd2 x)))
