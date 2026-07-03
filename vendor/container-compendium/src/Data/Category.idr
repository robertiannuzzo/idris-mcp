module Data.Category

import Decidable.Equality
import public Data.Category.Ops

import public Proofs

%default total

private infixr 7 ~:>
private infixl 5 |:>
%hide Prelude.(|>)
public export
record Category (o : Type) where
  constructor MkCategory
  0 (~:>) : o -> o -> Type
  id : (v : o) -> v ~:> v
  (|:>) : {a, b, c : o} -> (a ~:> b) -> (b ~:> c) -> (a ~:> c)
  0 idRight : (a, b : o) -> (f : a ~:> b) -> f |:> id b ≡ f
  0 idLeft  : (a, b : o) -> (f : a ~:> b) -> id a |:> f ≡ f
  0 compAssoc : (a, b, c, d : o) ->
                (f : a ~:> b) ->
                (g : b ~:> c) ->
                (h : c ~:> d) ->
                f |:> (g |:> h) ≡ (f |:> g) |:> h
public export
0 (~>) : (cat : Category o) => o -> o -> Type
(~>) = Category.(~:>) cat
public export
(|>) : (cat : Category o) => {a, b, c : o} ->
       a ~> b -> b ~> c -> a ~> c
(|>) = Category.(|:>) cat
public export
NewCat :
  (0 objects : Type) ->
  (0 morphisms : objects -> objects -> Type) ->
  (identity : (x : objects) -> morphisms x x) ->
  (composition : {a, b, c : objects} ->
    morphisms a b -> morphisms b c -> morphisms a c) ->
  (0 identity_right : {a, b : objects} -> (f : morphisms a b) ->
      composition f (identity b) ≡ f) ->
  (0 identity_left : {a, b : objects} -> (f : morphisms a b) ->
      composition (identity a) f ≡ f) ->
  (0 compose_assoc : {a, b, c, d : objects} ->
      (f : morphisms a b) -> (g : morphisms b c) -> (h : morphisms c d) ->
      composition f (composition g h) ≡ composition (composition f g) h) ->
  Category objects
NewCat _ m i c ir il a =
  MkCategory m i c (\_, _ => ir) (\_, _ => il) (\_, _, _, _ => a)
public export
(.idswap) : (cat : Category o) -> (a, b : o) -> (m : a ~> b) -> (cat.id a |> m) {cat, a, b=a, c=b} ≡ (m |> cat.id b){cat, a, b, c=b}
(.idswap) cat a b m = trans (cat.idLeft {}) (sym $ cat.idRight {})
public export
(.op) : Category o -> Category o
(.op) cat = NewCat
    { objects = o
	  , morphisms = (\x, y => y ~> x)
    , identity = cat.id
    , composition = (\f, g => (|:>) cat g f )
    , identity_left = \f => cat.idRight _ _ f
    , identity_right = \f => cat.idLeft _ _ f
    , compose_assoc = (\f, g, h => sym (cat.compAssoc _ _ _ _ h g f))
    }
public export
DiscreteCat : Category o
DiscreteCat = NewCat
  { objects = o
  , morphisms = (\x, y => x === y)
  , identity = (\_ => Refl)
  , composition = (\f,g => trans f g)
  , identity_right = (\Refl => Refl)
  , identity_left = (\Refl => Refl)
  , compose_assoc = (\_, _, _ => UIP {})
  }
public export
OneCat : Category Unit
OneCat = NewCat
  { objects = ()
  , morphisms = (\x, y => Unit)
  , identity = (\_ => ())
  , composition = (\_,_ => ())
  , identity_right = (\() => Refl)
  , identity_left = (\() => Refl)
  , compose_assoc = (\_, _, _ => Refl)
  }
public export
Set : Category Type
Set = NewCat
  { objects = Type
  , morphisms = (\a, b => a -> b)
  , identity = (\_ => id)
  , composition = (\f, g => g . f)
  , identity_right = (\_ => Refl)
  , identity_left = (\_ => Refl)
  , compose_assoc = (\_, _, _ => Refl)
  }
public export
(.obj) : {o : Type} ->  Category o -> Type
(.obj) _ = o
