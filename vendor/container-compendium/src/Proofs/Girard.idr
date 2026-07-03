module Proofs.Girard

import Data.Sigma
%default total

-- a Set as a pair of a type and a predicate over that type
data Set : Type where
  MkSet : (x : Type) -> (x -> Set) -> Set

-- Ensure a set is an element of another set
Elem : Set -> Set -> Type
Elem a (MkSet b p) = (Σ (x : b) |  a === p x)

-- Ensure a set is _not_ an element of another set
NotElem : Set -> Set -> Type
NotElem a b = Not (a `Elem` b)

-- Ensure a set is not contained in itself
NotSelf : Set -> Type
NotSelf a = NotElem a a

-- The set of "sets that do not contain themselves"
SetNotItself : Set
SetNotItself = MkSet (Σ (s : Set) | NotSelf s) π1

-- if a set is in `SetNotItself` then it doesn't contain itself
SetNotItselfNotItself : {a_set : Set} -> a_set `Elem` SetNotItself -> NotSelf a_set
SetNotItselfNotItself ((_ ## p) ## Refl) = p

-- The set of "sets that do not contain themselves" does not contain itself
NotItself : NotSelf SetNotItself
NotItself set = SetNotItselfNotItself set set

-- If a set does not contain itself, then it must be an element of `SetNotItSelf`
NotItselfIsSetNotItself : {a_set : Set} -> NotSelf a_set -> a_set `Elem` SetNotItself
NotItselfIsSetNotItself p = ((a_set ## p) ## Refl)

-- The set of "sets that do not contain themselves" cannot be both in `SetNotItself`
-- and also not contain itself.
False : Void
False = NotItself (NotItselfIsSetNotItself NotItself)
