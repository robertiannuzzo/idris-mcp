||| Comma categories
||| A comma category is built from two functors with the same codomain
||| To define it we need:
||| - three categories left, right, middle
||| - two functors `F1 : left => middle`, `F2 : right => middle`
|||
||| The object of the comma category are triples (a, b, F1 a -> F2 b) where
||| `a` is an object of left, `b` is an object of `right`, and the last
||| element is a morphism in the `middle` category after transporting each
||| element using functors `F1` and `F2`
module Data.Category.Comma

import Data.Category
import Data.Category.Functor
import Data.Sigma

import Proofs.Extensionality
import Proofs.Congruence
import Proofs.UIP

import Syntax.PreorderReasoning

%unbound_implicits off
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Functor

||| First we define objects as triple of an object in each of the "side"
||| categories and a morphism in the "middle" category.
public export
record CommaObject
    {0 o1, o2, o3 : Type}
    {0 left : Category o1}
    {0 middle : Category o2}
    {0 right : Category o3}
    {0 f1 : left ->> middle}
    {0 f2 : right ->> middle} where
  constructor MkCommaObj
  obj1 : o1
  obj2 : o3
  mor : f1.mapObj obj1 ~> f2.mapObj obj2

||| A morphism between comma-objects (x, y, m1) and (v, w, m2)
||| is also a triple.
||| The first element is a morphism `f` in the left category
||| The second element is a morphism `g` in the right category
||| and the final one is a commutative square linking m1 and m2:
|||            f
|||       x -------> y
|||            g
|||       v -------> w
|||
|||          F1 f
|||   F1 x -------> F1 y
|||     |             |
|||     |             |
|||  m1 |             | m2
|||     |             |
|||     V             V
|||   F2 v -------> F2 w
|||          F2 g
|||
public export
record CommaMorphism {0 o1, o2, o3 : Type}
                     {0 left : Category o1}
                     {0 middle : Category o2}
                     {0 right : Category o3}
                     {0 f1 : left ->> middle}
                     {0 f2 : right ->> middle}
                     (a, b : CommaObject {left, middle, right, f1, f2}) where
  constructor MkCommaMor
  f : a.obj1 ~> b.obj1
  g : a.obj2 ~> b.obj2
  0 commutes : let
      0 top : f1.mapObj a.obj1 ~> f1.mapObj b.obj1
      top = f1.mapHom _ _ f
      0 bot : f2.mapObj a.obj2 ~> f2.mapObj b.obj2
      bot = f2.mapHom _ _ g
      0 right : f1.mapObj b.obj1 ~> f2.mapObj b.obj2
      right = b.mor
      0 left : f1.mapObj a.obj1 ~> f2.mapObj a.obj2
      left = a.mor
      0 topRight : f1.mapObj a.obj1 ~> f2.mapObj b.obj2
      topRight = top |> right
      0 leftBot : f1.mapObj a.obj1 ~> f2.mapObj b.obj2
      leftBot = left |> bot
   in topRight === leftBot

||| An equality of comma-morphisms is given by the equality
||| of their morphisms.
public export
record CommaMorEq
    {0 o1, o2, o3 : Type}
    {0 left : Category o1}
    {0 middle : Category o2}
    {0 right : Category o3}
    {0 f1 : left ->> middle}
    {0 f2 : right ->> middle}
    {a, b : CommaObject {left, middle, right, f1, f2}}
    (m1, m2 : CommaMorphism a b) where
  constructor MkCommaMorEq
  0 same_f : m1.f === m2.f
  0 same_g : m1.g === m2.g


parameters
    {0 o1, o2, o3 : Type}
    {left : Category o1}
    {0 middle : Category o2}
    {right : Category o3}
    {0 f1 : left ->> middle}
    {0 f2 : right ->> middle}

  ||| An equality of comma-morphisms can be converted to an equality
  ||| by rewriting each equality on morphisms, the commutativity square
  ||| holds by uniqueness of identity proofs.
  public export 0
  CommaMorEqToEq : {a, b : CommaObject {left, middle, right, f1, f2}} ->
                   {m1, m2 : CommaMorphism {left, middle, right, f1, f2} a b} ->
                   CommaMorEq {left, middle, right, f1, f2} m1 m2 ->
                   m1 === m2
  CommaMorEqToEq {m1 =MkCommaMor m1f m1g m1p, m2=MkCommaMor m2f m2g m2p} (MkCommaMorEq sf sg) =
    rewrite sf in rewrite sg
    in cong (\x => MkCommaMor m2f m2g x) (UIP _ _)

  ||| The identity morphism on comma-morphisms
  export
  identity : (a : CommaObject {o1, o2, o3, left, middle, right, f1, f2} ) ->
             CommaMorphism {o1, o2, o3, left, middle, right, f1, f2} a a
  identity a = MkCommaMor
      (left.id a.obj1)
      (right.id a.obj2)
      (let proof1 = f1.presId a.obj1
           proof2 = sym (f2.presId a.obj2)
           proof4 = middle.idLeft
       in Calc $ |~ (f1.mapHom a.obj1 a.obj1
                           (left.id a.obj1) |> a.mor)
                 ~~ (middle.id (f1.mapObj a.obj1) |> a.mor)
                 ...(cong (\fx => fx |> a.mor) proof1)

                 ~~ a.mor
                 ...(middle.idLeft _ _ a.mor)

                 ~~ (a.mor |> middle.id (f2.mapObj a.obj2))
                 ..<(middle.idRight _ _ a.mor)

                 ~~ (a.mor |> f2.mapHom a.obj2 a.obj2
                                    (right.id a.obj2))
                 ...(cong ((|:>) middle a.mor) proof2))

  ||| Composition of comma-morphisms
  export
  compose : (a, b, c : CommaObject {left, middle, right, f1, f2}) ->
            CommaMorphism a b ->
            CommaMorphism b c ->
            CommaMorphism a c
  compose a b c x y = MkCommaMor
      (x.f |> y.f)
      (x.g |> y.g)
      (let sq1 = x.commutes
           sq2 = y.commutes
           fm = f1.presComp _ _ _ x.f y.f
           fn = sym (f2.presComp _ _ _ x.g y.g)
        in Calc $ |~ ((fmap {f=f1} (x.f |> y.f)) |> c.mor)
                  ~~ ((fmap {f=f1} x.f |> fmap y.f) |> c.mor)
                  ...(cong (\fx => fx |> c.mor) fm)

                  ~~ (fmap {f=f1} x.f |> (fmap y.f |> c.mor))
                  ..<(middle.compAssoc _ _ _ _ (fmap x.f) (fmap y.f) c.mor)

                  ~~ (fmap x.f |> (b.mor |> fmap y.g))
                  ...(cong (\fx => f1.mapHom a.obj1 b.obj1 x.f |> fx) sq2)

                  ~~ ((fmap x.f |> b.mor) |> fmap y.g)
                  ...(middle.compAssoc _ _ _ _ (fmap x.f) b.mor (fmap y.g))

                  ~~ ((a.mor |> fmap x.g) |> fmap y.g)
                  ...(cong (\fx => fx |> fmap y.g) sq1)

                  ~~ (a.mor |> (fmap x.g |> fmap y.g))
                  ..<(middle.compAssoc _ _ _ _ a.mor (fmap x.g) (fmap y.g))

                  ~~ a.mor |> (fmap {f=f2} (x.g |> y.g))
                  ...(cong (a.mor |>) fn))

  ||| Composing with identity is neutral
  export
  idLeftComma :
      {a, b : CommaObject} ->
      (mor : CommaMorphism a b) ->
      compose a b b mor (identity {a=b}) `CommaMorEq` mor
  idLeftComma mor = MkCommaMorEq (left.idRight _ _ _) (right.idRight _ _ _)

  ||| Composing with identity is neutral
  export
  idRightComma :
      {a, b : CommaObject} ->
      (mor : CommaMorphism a b) ->
      compose a a b (identity a) mor `CommaMorEq` mor
  idRightComma mor = MkCommaMorEq (left.idLeft _ _ _) (right.idLeft _ _ _)

  ||| Composition of comma-morphisms is associative
  export
  commaCompAssoc :
    {0 a, b, c, d : CommaObject} ->
    (f : CommaMorphism a b) ->
    (g : CommaMorphism b c) ->
    (h : CommaMorphism c d) ->
    compose a b d f (compose b c d g h) `CommaMorEq`
    compose a c d (compose a b c f g) h
  commaCompAssoc f g h = MkCommaMorEq
      (left.compAssoc _ _ _ _ _ _ _)
      (right.compAssoc _ _ _ _ _ _ _)

||| A Comma-category built fom two functors
public export
Comma : {0 o1, o2, o3 : Type} ->
        {left : Category o1} ->
        {middle : Category o2} ->
        {right : Category o3} ->
        (f1 : left ->> middle) ->
        (f2 : right ->> middle) ->
        Category (CommaObject {left, middle, right, f1, f2})
Comma f1 f2 = MkCategory
  CommaMorphism
  (\x => identity x)
  (compose _ _ _)
  (\_, _, m => CommaMorEqToEq (idLeftComma m))
  (\_, _, m => CommaMorEqToEq (idRightComma m))
  (\_, _, _, _, f, g, h => CommaMorEqToEq (commaCompAssoc f g h))

public export
Slice : {0 o1, o2 : Type} ->
        {left : Category o1} ->
        {middle : Category o2} ->
        (f1 : left ->> middle) ->
        Category (CommaObject {left, middle, right=middle, f1, f2 = idF middle})
Slice f1 = Comma f1 (idF middle)
