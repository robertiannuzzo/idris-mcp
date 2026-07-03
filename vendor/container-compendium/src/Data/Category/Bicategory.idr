module Data.Category.Bicategory

import Data.Sigma
import Data.Category
import Data.Category.Monoid
import Data.Category.Bifunctor
import Data.Category.NaturalTransformation

%unbound_implicits off
public export
record Bicategory (o : Type {- 0-cells -}) where
  constructor MkBiCat

  -- 1-cells
  0 m : o -> o -> Type

  -- vertical morphisms which morphisms are the 2-cells
  vert : (a, b : o) -> Category (m a b)

  -- horizontal morphisms
  horz : (a, b, c : o) -> Bifunctor (vert a b) (vert b c) (vert a c)

%unbound_implicits on

||| A helper to extract 2-cells out of a bicategory
public export 0
two_cell : forall o. (bc : Bicategory o) => {0 a, b : o} -> bc.m a b -> bc.m a b -> Type
two_cell x y = (~:>) (bc.vert a b) x y
