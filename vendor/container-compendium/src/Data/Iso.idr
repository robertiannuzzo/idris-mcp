module Data.Iso

import Control.Relation

import Data.Product
import Data.Coproduct

import Proofs.Extensionality
import Proofs.UIP
import Control.Order
import public Data.Ops

-- an abstract implementation of Iso for any preorder relation
public export
record (≅) (left, right : Type) where
  constructor MkIso
  to : left -> right
  from : right -> left
  0 toFrom : (x : right) -> to (from x) === x
  0 fromTo : (x : left) -> from (to x) === x
public export
identity : (0 x : Type) -> x ≅ x
identity x = MkIso
  id
  id
  (\_ => Refl)
  (\_ => Refl)
public export
symIso : x ≅ y -> y ≅ x
symIso (MkIso to from toFrom fromTo) = MkIso from to fromTo toFrom
public export
transIso : {0 x, y, z : Type} -> x ≅ y -> y ≅ z -> x ≅ z
transIso iso1 iso2 =
  MkIso
    (iso2.to . iso1.to)
    (iso1.from . iso2.from)
    (\v => cong iso2.to (iso1.toFrom (iso2.from v)) `trans` iso2.toFrom v)
    (\v => trans (cong iso1.from (iso2.fromTo (iso1.to v))) (iso1.fromTo v))
export
Reflexive Type (≅) where
  reflexive = identity _

export
Transitive Type (≅) where
  transitive = transIso

export
Symmetric Type (≅) where
  symmetric = symIso

export
Equivalence Type (≅) where
public export
record IsoEq (i1, i2 : left ≅ right) where
  constructor MkIsoEq
  0 eqTo : (x : left) -> i1.to x === i2.to x
  0 eqFrom : (x : right) -> i1.from x === i2.from x
isoEqToEq : IsoEq a b -> a === b
export
reflIsoEq : IsoEq a a
reflIsoEq = MkIsoEq
  (\_ => Refl)
  (\_ => Refl)
export
symIsoEq : IsoEq a b -> IsoEq b a
symIsoEq (MkIsoEq et tf) = MkIsoEq (\x => sym (et x)) (\x => sym (tf x))
export
trans : IsoEq a b -> IsoEq b c -> IsoEq a c
export
transIsoAssoc : {0 a, b, c, d : Type} ->
                 (f : a ≅ b) -> (g : b ≅ c) -> (h : c ≅ d) ->
                 (f `transIso` (g `transIso` h)) `IsoEq`
                 ((f `transIso` g) `transIso` h)
transIsoAssoc f g h = MkIsoEq (\x => Refl) (\_ => Refl)
export
isoIdRight : (f : a ≅ b) -> transIso f (identity b) `IsoEq` f
isoIdRight (MkIso to from toFrom fromTo) = MkIsoEq (\_ => Refl) (\_ => Refl)

export
isoIdLeft : (f : a ≅ b) -> transIso (identity a) f `IsoEq` f
isoIdLeft (MkIso to from toFrom fromTo) = MkIsoEq (\_ => Refl) (\_ => Refl)
public export
IsoVoid : (u1 : Uninhabited a) => (u2 : Uninhabited b) => a ≅ b
IsoVoid = MkIso absurd absurd  (\x => absurd x) (\x => absurd x)
export
idTo : (x : a) -> ((identity a).to x) = x
idTo x = Refl

export
idFrom : (x : a) -> ((identity a).from x) = x
idFrom x = Refl


export
congIso : {0 t1, s1 : Type} ->
          {0 f1, f2 : t1 -> s1} ->
          {0 b1, b2 : s1 -> t1} ->
          {0 fb1 : (x : s1) -> f1 (b1 x) === x} ->
          {0 fb2 : (x : s1) -> f2 (b2 x) === x} ->
          {0 bf1 : (x : t1) -> b1 (f1 x) === x} ->
          {0 bf2 : (x : t1) -> b2 (f2 x) === x} ->
          (p1 : f1 === f2) ->
          (p2 : b1 === b2) ->
          (p3 : fb1 === (rewrite p1 in rewrite p2 in fb2)) ->
          (p4 : bf1 === (rewrite p2 in rewrite p1 in bf2)) ->
          MkIso f1 b1 fb1 bf1 === MkIso f2 b2 fb2 bf2
congIso Refl Refl Refl Refl = Refl

export
0 fromIsoEq : (a, b : left ≅ right) -> IsoEq a b -> a === b
fromIsoEq (MkIso to1 from1 _ _) (MkIso to2 from2 _ _)
    (MkIsoEq eqTo eqFrom ) = congIso (funExt eqTo) (funExt eqFrom) (funExtDep $ \_ => UIP _ _) (funExtDep $ \_ => UIP _ _)

export
transIsoTo : (transIso iso1 iso2).to vx === iso2.to (iso1.to vx)
transIsoTo = Refl


public export
IsoCoprod : a ≅ b -> x ≅ y -> (a + x) ≅ (b + y)
IsoCoprod iso1 iso2 = MkIso
  (bimap iso1.to iso2.to)
  (bimap iso1.from iso2.from)
  (\case (+> r) => cong (+>) (iso2.toFrom r)
         (<+ l) => cong (<+) (iso1.toFrom l))
  (\case (+> r) => cong (+>) (iso2.fromTo r)
         (<+ l) => cong (<+) (iso1.fromTo l))

public export
IsoProd : a ≅ b -> x ≅ y -> (a * x) ≅ (b * y)
IsoProd iso1 iso2 = MkIso
  (bimap iso1.to iso2.to)
  (bimap iso1.from iso2.from)
  (\(x && y) => cong2 (&&) (iso1.toFrom x) (iso2.toFrom y))
  (\(x && y) => cong2 (&&) (iso1.fromTo x) (iso2.fromTo y))
liftProof : {0 x, y : a} -> (iso : a ≅ b) -> x === y -> iso.to x === iso.to y
liftProof iso Refl = Refl


export
appIso : {0 a, b : Type} ->
         {0 g : b -> Type} ->
         (iso : a ≅ b) ->
         ((val : a) -> g (to iso val)) ->
         (vx : b) -> (vz : a) -> vz === from iso vx ->
         g vx
appIso iso f vx (from iso vx) Refl =
  replace {p = g} (iso.toFrom vx) (f $ from iso vx)

export
appIsoId : {a : Type} -> {g : a -> Type} -> (vx : (x : a) -> g x) ->
           (gx : a) ->
           appIso {a, b = a, g} (identity a) vx gx gx Refl = vx gx
appIsoId vx gx = Refl

export
appIsoId' : {a : Type} -> {g : a -> Type} -> (vx : (x : a) -> g x) ->
           (gx : a) -> (gy : a) -> (prf : gy === from (identity a) gx) ->
           (===) (appIso {a, b = a, g} (identity a) vx gx gy prf) (vx gx)
               {a = g gx}
appIsoId' vx gx gx Refl = Refl
