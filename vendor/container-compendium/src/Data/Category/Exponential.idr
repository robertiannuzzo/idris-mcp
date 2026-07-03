module Data.Category.Exponential

import Data.Category
import Data.Category.Product

%hide Prelude.Ops.infixl.(|>)
private infix 1 :⇒
public export
record ExponentialObject {0 o : Type} (cat : Category o) (prod : HasProduct cat) where
  constructor MkExp
  (:⇒) : o -> o -> o
  eval : (z, y : o) -> (y :⇒ z) >< y ~> z
  curry : (x, y, z : o) ->
          (g : (x >< y) ~> z) ->
          x ~> (y :⇒ z)

  triangle : (x, y, z : o) ->
             (g : (x >< y) ~> z) ->
             let λg : x ~> (y :⇒ z)
                 λg = curry x y z g
                 0
                 compose : (x >< y) ~> (y :⇒ z) >< y ->
                           (y :⇒ z) >< y ~> z ->
                           (x >< y) ~> z
                 compose = (|:>) cat
                 0
                 curried : (x >< y) ~> (y :⇒ z) >< y
                 curried = λg ~><~ cat.id y
             in (curried `compose` eval z y) === g

{-

  ||| (arrow : x ~> x') -> lam (arrow -.- id) |> g = arrow |> lam g
  naturalLam : {x, x', y, z : o} ->
               (arrow : x ~> x') ->
               (g : (x' >< y) ~> z) ->
               (lam x y z
                     (Start ((x >< y) -< ((-.-) {a=x} {b=x'} {c=y} {d=y} arrow (cat.id {v=y})) >-
                            (x' >< y) -< g >- End z)))
               ===
                 Start (x -< arrow >- x' -< lam x' y z g >- End (z ^^ y))

