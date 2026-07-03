module Data.Category.Monad.Cartesian

import Data.Category
import Data.Category.Functor
import Data.Category.Monad
import Data.Category.Endofunctor
import Data.Category.NaturalTransformation
import public Data.Category.Pullback

%unbound_implicits off
public export
record CartesianMonad {0 o : Type} (c : Category o) (F : Endo c) where
  constructor MkCartMonad
  m : Monad c F
  --   x -------> F x
  --   |           |
  --   |           | F m
  --   V           V
  --   y -------> F y
  --          mult
  unitPullback : (x, y : o) -> (f : x ~> y) ->
      Pullback {o, c} (MkSpan {o, c} (F .mapObj x) y (F .mapObj y) (F .mapHom x y f) (m.unit.component y))
  -- F (F x) ------> (F x)
  --   |               |
  --   |               | F m
  --   V               V
  -- F (F y) -------> F y
  --          mult
  multPullback : (x, y : o) -> (f : x ~> y) ->
      Pullback {o, c} (MkSpan {o, c} (F .mapObj x) (F .mapObj (F .mapObj y)) (F .mapObj y) (F .mapHom x y f) (m.mult.component y))
