||| All interpretations of dependent lenses as data accessors are here
module Data.Container.Morphism.Affine

import Optics.Lens
import Optics.Prism

import Data.Product
import Data.Boundary
import Data.Coproduct
import Data.Sigma
import Data.Container.Morphism
import Data.Container.Descriptions.Maybe
import Data.Container.Descriptions.List
import Data.Iso
import Data.Vect

import Proofs.Extensionality
import Proofs.Congruence
import Proofs.Sigma
import Proofs.Unit
import Proofs.Void

import Control.Function

%default total

%unbound_implicits off
---------------------------------------------------------------------------------
-- Affine traversal is isomorphic to the Maybe Monad on Container
---------------------------------------------------------------------------------

affineX : {x : _} -> MkAffine (x.read) === x
affineX {x = MkAffine r} = Refl

%unbound_implicits off
parameters {0 a, a', b, b' : Type}

  readImpl :
             {fwd : a -> Ex MaybeCont b} ->
             {bwd : (x : a) -> (IsTrue ((fwd x).ex1) -> b') -> a'} ->
             a -> a' + (b * (b' -> a'))
  readImpl {fwd} {bwd} x with (fwd x) proof p
    readImpl x | (MkEx False p2) = <+ (bwd x (replace
                {p = \x : MaybeType b => IsTrue x.ex1 -> b'}
                (sym p)
                absurd))
    readImpl x | (MkEx True p2) = +> (p2 T && \bv => bwd x (rewrite p in const bv))

  maybeIsAffine : (a :- a') =%> MaybeCont ▶ (b :- b') -> Affine (MkB a a') (MkB b b')
  maybeIsAffine mor =
    MkAffine (readImpl {fwd = mor.fwd, bwd=mor.bwd})


  just : (aff : a -> a' + (b * (b' -> a'))) ->
         a -> Ex MaybeCont b
  just aff x = case aff x of
               (<+ y) => Nothing
               (+> y) => Just y.π1

  recover : (aff : a -> a' + (b * (b' -> a'))) ->
            (v : a) -> (IsTrue (just aff v).ex1 -> b') -> a'
  recover aff v f with (aff v)
    recover aff v f | (<+ x) = x
    recover aff v f | (+> x) = x.π2 (f T)

  affineIsMaybe : Affine (MkB a a') (MkB b b') -> (a :- a') =%> MaybeCont ▶ (b :- b')
  affineIsMaybe aff = MkMorphism
      (just aff.read)
      (recover aff.read)

  exInj : {0 t : Type} -> {0 p : Container} -> {0 a, c : p.shp} -> {0 b : p.pos a -> t} -> {0 d : p.pos c -> t} ->
          MkEx a b = MkEx {cont = p} c d -> a = c
  exInj Refl = Refl

  exInj2 : {0 t : Type} -> {0 p : Container} -> {0 a : p.shp} -> {0 b, c : p.pos a -> t} ->
           MkEx a b = MkEx {cont = p} a c -> b = c
  exInj2 Refl = Refl

  lemma1 : (x : Affine (MkB a a') (MkB b b')) -> maybeIsAffine (affineIsMaybe x) = x
  lemma1 x = (cong MkAffine $ funExt $ lemma11) `trans` affineX {x}
    where
      0 lemma11 : (v : a) -> readImpl {fwd = fwd (affineIsMaybe x), bwd = bwd (affineIsMaybe x)} v === x.read v
      lemma11 v with (fwd (affineIsMaybe x) v) proof p'
        lemma11 v | (MkEx False p2) with (x.read v)
          lemma11 v | (MkEx False p2) | (<+ y) = Refl
          lemma11 v | (MkEx False p2) | (+> y) = absurd $ exInj p'
        lemma11 v | (MkEx True p2) with (x.read v) proof q'
          lemma11 v | (MkEx True p2) | (<+ y) = absurd $ exInj p'
          lemma11 v | (MkEx True p2) | (+> y) =
            let fnWrangling : p2 T === y.π1
                fnWrangling = rewrite sym (exInj2 p') in Refl
            in cong (+>) (cong2 (&&) fnWrangling Refl `trans` projIdentity y)


  0 lemma21 : {fwd : a -> Ex MaybeCont b} ->
              {bwd : (x : a) -> (IsTrue ((fwd x).ex1) -> b') -> a'} ->
              (x : a) -> (Accessor.just (Accessor.readImpl {fwd, bwd})) x = fwd x
  lemma21 {fwd} {bwd } x with (fwd x) proof pq
    lemma21 x | (MkEx True pp) = cong (MkEx True) (funExt $ \T => Refl)
    lemma21 x | (MkEx False pp) = cong (MkEx False) (allUninhabited absurd pp)

  0 lemma22 : {fwd : a -> Ex MaybeCont b} ->
              {bwd : (x : a) -> (IsTrue ((fwd x).ex1) -> b') -> a'} ->
              (x : a) -> (vx : IsTrue ((just (Accessor.readImpl {fwd,bwd}) x).ex1) -> b') ->
              let leftside : a'
                  leftside = Accessor.recover (Accessor.readImpl {fwd,bwd}) x vx
                  rightSide : a'
                  rightSide = bwd x (replace
                                 {p = \xa : MaybeType b => (IsTrue (xa.ex1) -> b')}
                                 (lemma21 {fwd, bwd, x})
                                 vx)
              in leftside === rightSide
  lemma22 {fwd} {bwd} x vx with (fwd x) proof pr
    lemma22 x vx | (MkEx True p) = cong (bwd x) (funExt $ rewrite pr in \T => Refl)
    lemma22 x vx | (MkEx False q) = cong (bwd x) (rewrite pr in allUninhabited absurd vx)

  0 lemma2 : (x : (a :- a') =%> MaybeCont ▶ (b :- b')) -> affineIsMaybe (maybeIsAffine x) = x
  lemma2 (MkMorphism fwd bwd) = cong2Dep' MkMorphism
    (funExt (lemma21 {fwd}))
    (funExtDep $ \x => funExt $ \vx => lemma22 {fwd, bwd} x vx)

  affineIso : ((a :- a') =%> MaybeCont ▶ (b :- b')) `Iso` (Affine (MkB a a') (MkB b b'))
  affineIso = MkIso
      maybeIsAffine
      affineIsMaybe
      lemma1
      lemma2


--   affineIsLinear : Affine (MkB a a') (MkB b b') -> Linear (a :- a') (MaybeCont ▶ (b :- b'))
--   affineIsLinear (MkAffine eff) = MkLin $
--     \v => case eff v of
--                <+ bval => Nothing ## const bval
--                +> bval => Just bval.π1 ## (\p => bval.π2 (p T))
--
--   linearIsAffine : Linear (a :- a') (MaybeCont ▶ (b :- b')) -> Affine (MkB a a') (MkB b b')
--   linearIsAffine (MkLin eff) = MkAffine $ \v =>
--       case eff v of
--            ((MkEx False p3) ## p2) => <+ (p2 absurd)
--            ((MkEx True p3) ## p2) => +> (p3 T && \bv => p2 (const bv))

record DepAffine (a, b : Container) where
  constructor MkAffine
  read : (x : a.shp) -> a.pos x + (Σ b.shp (\y => b.pos y -> a.pos x))
---------------------------------------------------------------------------------
-- Prisms are isomorphic to the Either Monad on Container from (t +)??
---------------------------------------------------------------------------------

EitherCont : Type -> Container
EitherCont ty = (!>) Bool (\case True => ty ; False => Void)

fromPrism : {0 a, b, s, t : Type} -> Prism a b s t -> (s :- t) =%> EitherCont t ▶ (a :- b)
fromPrism (MkPrism match build) = MkMorphism fwd bwd
  where
    fwd : s -> Ex (EitherCont t) a
    fwd x = case match x of
                 (<+ y) => MkEx False absurd
                 (+> y) => MkEx True (const y)
    bwd : (x : s) -> (EitherCont t ▶ (a :- b)).pos (fwd x) -> t
    bwd x f with (match x)
      bwd x f | (<+ y) = y
      bwd x f | (+> y) = build ?bwd_rhs_rhss_1

toPrism : {0 a, b, s, t : Type} -> (s :- t) =%> EitherCont t ▶ (a :- b) -> Prism a b s t
-- toPrism (MkMorphism part1 bwd) = MkPrism part1 ?toPrism_rhs_0bi
--   where
--     build : ((x : s) -> choice (\value => ()) (\value => b) (part1 x) -> t) -> b -> t
--     build f x = f (?bbb) ?build_rhs
