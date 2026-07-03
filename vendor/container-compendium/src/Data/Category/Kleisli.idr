module Data.Category.Kleisli

import Data.Category

%unbound_implicits off
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

record KTriple {0 o : Type} (cat : Category o) where
  constructor MkKleisli
  m : o -> o
  η : (0 x : o) -> x ~> m x
  star : {0 a, b : o} -> a ~> m b -> m a ~> m b
  0 idCheck : {0 x : o} -> star {a = x, b = x} (η x)  === cat.id (m x)
  0 idStar : {0 x, y : o} -> {0 f : x ~> m y} -> ((|:>) {a = x, b = m x, c = m y} cat (η x) (star {a=x, b=y} f)) === f
  0 compCheck : {0 x, y, z : o} -> {0 f : x ~> m y} -> {0 g : y ~> m z} ->
                (|:>) cat (star {a = x, b = y} f) (star {a = y, b = z} g) {a = m x, b = m y, c = m z} ===
                star {a = x, b = z} ((|:>) {a = x, b = m y, c = m z} cat f (star {a = y, b = z} g))

public export
KleisliCat : {0 o : Type} -> (cat : Category o) -> (k : KTriple cat) -> Category o
KleisliCat cat k = MkCategory
  (\o1, o2 => o1 ~> k.m o2)
  (\v => k.η v)
  (\f, g => f |> k.star g)
  (\_, _, f => let
      i1 = cat.idRight _ _ f
      tt = k.idCheck
    in (cong ((|:>) cat f) tt `trans` i1))
  (\_, _, f => k.idStar)
  ass
    where
      ass : (a, b, c, d : o) ->
            (f : a ~> k.m b) ->
            (g : b ~> k.m c) ->
            (h : c ~> k.m d) ->
            (f |> k.star {a=b, b=d} ((g |> k.star {a=c, b=d} h) {a = b, b = k.m c, c = k.m d})) {a = a, b = k.m b, c = k.m d}
            === (((f |> k.star {a=b, b = c} g) {a = a, b = k.m b, c = k.m c}) |> k.star {a=c, b=d} h) {a = a, b = k.m c, c = k.m d}
      ass a b c d f g h =
        let 0 p1 = k.compCheck {f = g, g = h}
            0 p2 = cat.compAssoc _ _ _ _ f (k.star g) (k.star h)
        in cong ((|:>) cat f) (sym p1) `trans` p2


