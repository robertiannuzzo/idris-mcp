module Proofs.Relation

import public Control.Relation
import public Control.Order

public export
interface Preorder a r => EqRel (0 a : Type) (0 r : Rel a) where
  constructor MkEqRel
  0 toEq : forall x, y. r x y -> x === y

export
Preorder a (===) where

export %hint
prop : {a : Type} -> EqRel a (===)
prop = MkEqRel id
