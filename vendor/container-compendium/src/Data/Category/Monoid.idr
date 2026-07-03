module Data.Category.Monoid

import public Data.Category
import public Data.Category.Bifunctor
import public Data.Category.Iso
import public Data.Category.Product
import public Data.Category.NaturalTransformation


%hide Prelude.Ops.infixl.(*>)
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

%default total
%unbound_implicits off

||| A monoidal category
public export
record Monoidal {0 o : Type} (c : Category o) where
  constructor MkMonoidal

  mult : Bifunctor c c c

  i : o
  alpha : let f1, f2 : (c × (c × c)) ->> c
              f1 = ((idF _) `pair` mult) ⨾⨾ mult
              f2 = assocR ⨾⨾ ((mult `pair` idF _) ⨾⨾ mult)
          in f1 =~= f2
  leftUnitor :
      let 0 leftAppliedMult : c ->> c
          leftAppliedMult = applyL {a = c, b = c, c} i mult
      in leftAppliedMult =~= idF c
  rightUnitor :
      let 0 rightAppliedMult : c ->> c
          rightAppliedMult = applyR i mult
      in rightAppliedMult =~= idF c
%unbound_implicits on
public export
(⊗) : {auto 0 cat : Category o} -> (mon : Monoidal cat) => o -> o -> o
(⊗) a b = mon.mult.mapObj (a && b)

public export 0
(-⊗-)  : {auto 0 cat : Category o} -> {0 x, y, a, b : o} -> (mon : Monoidal cat) =>
       x ~> y -> a ~> b -> x ⊗ a ~> y ⊗ b
(-⊗-) m1 m2 = mon.mult.mapHom (x && a) (y && b) (m1 && m2)
%unbound_implicits off
||| a monoid in a monoidal category
public export
record MonoidObject {0 o : Type} {cat : Category o} (mon : Monoidal cat) where
  constructor MkMonObj
  obj : o
  η : mon.i ~> obj
  mult : obj ⊗ obj ~> obj
  0 left : let 0 η_id_μ, λ : mon.i ⊗ obj ~> obj
               0 topMorphism : mon.i ⊗ obj ~> obj ⊗ obj
               topMorphism = η -⊗- cat.id obj
               η_id_μ = topMorphism |> mult
               λ = mon.leftUnitor.nat.component obj
            in η_id_μ === λ
  0 right : let 0 id_η_μ, ρ : obj ⊗ mon.i  ~> obj
                0 topMorphism : obj ⊗ mon.i  ~> obj ⊗ obj
                topMorphism = cat.id obj -⊗- η
                id_η_μ = topMorphism |> mult
                ρ  = mon.rightUnitor.nat.component obj
             in id_η_μ === ρ
  0 assoc : let
                0 botLeft : (obj ⊗ obj) ⊗ obj ~> obj
                botLeft = mult -⊗- cat.id obj |> mult
                0 assoc : ((obj ⊗ obj) ⊗ obj) ~> obj ⊗ (obj ⊗ obj)
                assoc = mon.alpha.tan.component (obj && (obj && obj))
                0 topRight : ((obj ⊗ obj) ⊗ obj) ~> obj
                topRight = assoc |> cat.id obj -⊗- mult |> mult
            in botLeft === topRight
