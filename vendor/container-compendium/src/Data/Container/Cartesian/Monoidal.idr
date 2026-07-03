module Data.Container.Cartesian.Monoidal

import Data.Category.Monoid
import Data.Category.Bifunctor

import Data.Container.Category
import Data.Container.Cartesian.Category
import Data.Container.Cartesian

import Data.Iso

fromCart : a =#> b -> a =%> b

fromLens :
   (fn : Bendo Cont) ->
   (a : Container * Container) ->
   (b : Container * Container) ->
   (f : (a .π1 =#> b .π1) * (a .π2 =#> b .π2))  ->
   fn.mapObj a =#> fn.mapObj b
fromLens (MkFunctor fobj fmap fid fcomp) a b (c1 && c2)
  = let
    xy = (fmap a b (fromCart c1 && fromCart c2))
  in MkCartDepLens
      xy.fwd
      (\xx => MkIso (xy.bwd xx) ?adio ?cc ?oqiwoi)


fromContMult : Bendo Cont -> Bendo ContCart
fromContMult bendo@(MkFunctor mapObj mapHom presId presComp) =
  MkFunctor
    mapObj
    (\a, b, f => fromLens bendo a b f)

    ?M3
    ?fromContMult_rhs_0

fromCont : Monoidal Cont -> Monoidal ContCart
fromCont (MkMonoidal mult i a b c) =
  let 0 mult : Bendo Cont := mult
      0 neutral : Container := i
      goalMult : Bendo ContCart := ?addK
  in MkMonoidal
    goalMult
    ?fromCont_rhs_2
    ?fromCont_rhs_3
    ?fromCont_rhs_4
    ?fromCont_rhs_5

