module Data.Category.Functor

import public Data.Category

import Syntax.PreorderReasoning

import Proofs

%hide Prelude.Functor
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixl.(*>)

%unbound_implicits off

public export
record (->>) {0 o1, o2 : Type} (c : Category o1) (d : Category o2) where
  constructor MkFunctor

  -- A way to map objects
  mapObj : o1 -> o2

  -- A way to map morphisms
  -- For each morphism in C between objects x and y
  -- we get a morphism in D between the corresponding objects x and y
  -- but mapped to their counterparts in d
  mapHom : (x, y : o1) -> x ~> y -> mapObj x ~> mapObj y
  -- mapping the identity morphism in C results in the identity morphism in D
  0 presId : (v : o1) -> mapHom v v (c.id v) = d.id (mapObj v)
  0 presComp :
    (x, y, z : o1) -> -- given three objects x, y, z
    (f : x ~> y) ->   -- a morphism x -> y
    (g : y ~> z) ->   -- and a morphism y -> z

    let 0 f1, f2 : mapObj x ~> mapObj z
        -- Mapping the morphism after composition
        f1 = mapHom x z (f |> g)
        -- And composing the maps of each morphism
        f2 = mapHom x y f |> mapHom y z g
    in f1 === f2 -- Are the same thing
public export
(⨾⨾) : {0 o1, o2, o3 : Type} -> {0 a : Category o1} -> {0 b : Category o2} -> {0 c : Category o3} ->
      a ->> b -> b ->> c -> a ->> c
(⨾⨾) f1 f2 = MkFunctor
  (f2.mapObj . f1.mapObj)
  (\a, b, m => f2.mapHom (f1.mapObj a) (f1.mapObj b) (f1.mapHom a b m))
  (\x => cong (f2.mapHom (f1.mapObj x) (f1.mapObj x)) (f1.presId x)
        `trans` f2.presId (f1.mapObj x))
  (\a, b, c, h, j =>
      cong (f2.mapHom (f1.mapObj a) (f1.mapObj c)) (f1.presComp a b c h j) `trans`
      f2.presComp _ _ _ (f1.mapHom a b h) (f1.mapHom b c j))
public export
fmap : {0 o1, o2 : Type} ->
       {c1 : Category o1} -> {c2 : Category o2} -> {f : c1 ->> c2} ->
       {a, b : o1} ->
       a ~> b -> f.mapObj a ~> f.mapObj b
fmap x = mapHom f a b x
public export
idF : {0 o : Type} -> (0 c : Category o) -> c ->> c
idF c = MkFunctor id (\_, _ => id) (\_ => Refl) (\_, _, _, _, _ => Refl)
public export
Const : {0 o : Type} -> o -> (c : Category o) -> OneCat ->> c
Const x c = MkFunctor
    (const x) (\_, _, _ => c.id x) (\_ => Refl)
    (\_, _, _, _, _ => sym $ c.idLeft _ _ (c.id x) )
public export
(.op) : {0 a, b : _} -> a ->> b -> a.op ->> b.op
(.op) func = MkFunctor
    func.mapObj
    (\a, b => func.mapHom b a)
    func.presId
    (\x, y, z, f, g => func.presComp z y x g f)
public export
record FullyFaithful {o1, o2 : Type} {c : Category o1} {d : Category o2} (f : c ->> d) where
  constructor MkFullFaithful
  inv : {x, y : o1} -> f.mapObj x ~> f.mapObj y -> x ~> y
  0 inv1 : {x, y : o1} -> (m : x ~> y) -> inv {x, y} (f.mapHom x y m) ≡ m
  0 inv2 : (x, y : o1) -> (m : f.mapObj x ~> f.mapObj y) -> f.mapHom x y (inv {x, y} m) ≡ m
