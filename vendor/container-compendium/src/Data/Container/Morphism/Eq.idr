module Data.Container.Morphism.Eq

import Data.Container.Definition
import Data.Container.Morphism.Definition

import Proofs
import public Proofs.Transport

import public Control.Relation
import public Control.Order
import Data.Iso.Generic

%hide Control.Relation.Rel

export infix 0 `DepLensEq`
export infix 0 <%≡%>

||| Two container morphisms are equal if their mapping on shapes are equal and their
||| mapping on positions are equal.
public export
record (<%≡%>) (a, b : dom =%> cod) where
  constructor MkDepLensEq
  0 eqFwd : (v : dom.req) -> a.fwd v === b.fwd v
  0 eqBwd : (v : dom.req) -> (y : cod.res (a.fwd v)) ->
          let 0 p1 : dom.res v
              p1 = a.bwd v y
              0 p2 : dom.res v
              p2 = b.bwd v (replace {p = cod.res} (eqFwd v) y)
          in p1 === p2


export
0 depLensEqToEq : {a, b : dom =%> cod} -> a <%≡%> b -> a === b
depLensEqToEq {a = (fwd1 <! bwd1)} {b = (fwd2 <! bwd2)} (MkDepLensEq eqFwd eqBwd) =
  cong2Dep' (<!)
      (funExt eqFwd)
      (funExtDep $ \x => funExt $ \y => eqBwd x y
      )

||| Two container morphisms are equal if their mapping on shapes are equal and their
||| mapping on positions are equal.
public export
record DepLensEqTr (a, b : dom =%> cod) where
  constructor MkDepLensEqTr
  0 eqFwd : (v : dom.req) -> a.fwd v === b.fwd v
  0 eqBwd : (v : dom.req) -> (y : cod.res (a.fwd v)) ->
          let 0 p1 : dom.res v
              p1 = a.bwd v y
              0 p2 : dom.res v
              p2 = b.bwd v (transport cod.res (eqFwd v) y)
          in p1 === p2

export
Reflexive (dom =%> cod) DepLensEqTr where
  reflexive = MkDepLensEqTr (\_ => Refl) (\xa, xb => cong (x.bwd xa) (sym $ applyTransport ? ?))

export
0 depLensEqTrToEq : {a, b : dom =%> cod} -> a `DepLensEqTr` b -> a === b
depLensEqTrToEq {a = (fwd1 <! bwd1)} {b = (fwd2 <! bwd2)} (MkDepLensEqTr eqFwd eqBwd) =
  cong2Dep' (<!)
      (funExt eqFwd)
      (funExtDep $ \x => funExt $ \y => let
          gg = eqBwd x y
          aa = Transport.applyTransport (cod.res) {prf = eqFwd x} y
          in trans gg (cong (bwd2 x) aa)
      )

-- Preoerder of equality between lenses
public export
Transitive (dom =%> cod) (<%≡%>) where
  transitive a b = MkDepLensEq (\v => transitive (a.eqFwd v) (b.eqFwd v))
      (\v, w => transitive
           (a.eqBwd v w)
           (b.eqBwd v (replace {p = cod.res} (a.eqFwd v) w)))

public export
Reflexive (dom =%> cod) (<%≡%>) where
  reflexive = MkDepLensEq (\_ => Refl) (\_, _ => Refl)

public export
Preorder (dom =%> cod) (<%≡%>) where

public export
Symmetric (dom =%> cod) (<%≡%>) where
  symmetric (MkDepLensEq eqFwd eqBwd) =
    MkDepLensEq (\x => sym (eqFwd x))
    (\a, b => sym $ eqBwd a (replace {p = cod.response} (sym $ eqFwd a) b) )

export 0
fromEq : p1 === p2 -> p1 <%≡%> p2
fromEq Refl = reflexive

||| An isomorphism of container morphisms
public export
ContIso : (x, y : Container) -> Type
ContIso = GenIso Container (=%>) (<%≡%>)

export
refl : ContIso a a
refl = MkGenIso (identity _) (identity _)
           (MkDepLensEq (\_ => Refl) (\_, _ => Refl))
           (MkDepLensEq (\_ => Refl) (\_, _ => Refl))

export
Reflexive Container ContIso where
    reflexive = refl

trans : ContIso x y -> ContIso y z -> ContIso x z
trans f g = MkGenIso
    (f.to |%> g.to)
    (g.from |%> f.from)
    (let fft = f.fromTo
         gft = g.fromTo
         ftf = f.toFrom
         gtf = g.toFrom
      in ?bkjb)
    ?trans_rhs

export
Transitive Container ContIso where
  transitive f g = trans f g

sym : ContIso x y -> ContIso y x
sym i = MkGenIso i.from i.to (let pp = i.fromTo in ?aaa)  (let xx = i.toFrom in ?bbb)

export
Symmetric Container ContIso where
    symmetric = sym

export
[ContIsoPre] Preorder Container ContIso where

