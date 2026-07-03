module Proofs.Maybe

import Proofs.Relation
import Control.Relation

public export
data MaybeEq : EqRel a rel -> (x, y : Maybe a)  -> Type where
  NothingIsNothing : MaybeEq eq Nothing Nothing
  JustIsJust : {eq : EqRel a rel} -> (x, y : a) -> (0 _ : x `rel` y) -> MaybeEq eq (Just x) (Just y)

public export
MaybeEq' : (x, y : Maybe a) -> Type
MaybeEq' = MaybeEq {rel = Equal} (MkEqRel id)

export 0
maybeEqToEq : MaybeEq eqRel x y -> x === y
maybeEqToEq NothingIsNothing = Refl
maybeEqToEq (JustIsJust {eq} z w prf) = cong Just (toEq @{eq} prf)

export
{eqRel : EqRel a rel} -> Transitive (Maybe a) (MaybeEq eqRel) where
  transitive NothingIsNothing b = b
  transitive (JustIsJust w v s) (JustIsJust v u x1)
      = let 0 rrr = transitive s x1
            vv = JustIsJust {rel } w u rrr in vv

export
{eqRel : EqRel a rel} -> Reflexive (Maybe a) (MaybeEq eqRel) where
  reflexive {x = Nothing} = NothingIsNothing
  reflexive {x = (Just x)} = JustIsJust x x reflexive

export
{eqRel : EqRel a rel} -> Preorder (Maybe a) (MaybeEq eqRel) where

export
{eqRel : EqRel a rel} -> EqRel (Maybe a) (MaybeEq eqRel) where
  toEq = maybeEqToEq
